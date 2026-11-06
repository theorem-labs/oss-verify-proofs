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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_025S9 BndP_Eb_026S9 BndP_Eb_024S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENTBP.
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

Module Pbntbu16A := BndP_Eb_025S9.LibSegEb_bntbu16A.
Definition KS_bntbu16A : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu16A.regs0 Pbntbu16A.regs_out0).
Lemma KS_bntbu16A_ok : BG.kept_ok 80 Pbntbu16A.regs0 Pbntbu16A.regs_out0 KS_bntbu16A = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu16A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1bc4 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bntbu16A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 728112
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pbntbu16A.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu16A.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu16A.kn0).
  { unfold know_ok, Pbntbu16A.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu16A.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu16A.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pbntbu16A.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu16A.ps0) with 0x5ec3c in Hms. change (SR.ps_regs Pbntbu16A.ps0) with (map (fun i => (i, nth i Pbntbu16A.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu16A.ps0) with Pbntbu16A.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu16A.regs0 Pbntbu16A.regs_out0 80 KS_bntbu16A KS_bntbu16A_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbu16A.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pbntbu16B := BndP_Eb_025S9.LibSegEb_bntbu16B.
Definition KS_bntbu16B : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu16B.regs0 Pbntbu16B.regs_out0).
Lemma KS_bntbu16B_ok : BG.kept_ok 80 Pbntbu16B.regs0 Pbntbu16B.regs_out0 KS_bntbu16B = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu16B_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1c30 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbu16B -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 728316
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 91)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 90)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G19 G20 G21 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 33%nat => Z_to_bv 64 vz_33 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 33%nat => vz_33 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbu16B.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu16B.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu16B.kn0).
  { unfold know_ok, Pbntbu16B.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu16B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu16B.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pbntbu16B.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu16B.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbu16B.ps0) with (map (fun i => (i, nth i Pbntbu16B.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu16B.ps0) with Pbntbu16B.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu16B.regs0 Pbntbu16B.regs_out0 80 KS_bntbu16B KS_bntbu16B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16B.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbu16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbu16M := BndP_Eb_025S9.LibSegEb_bntbu16M.
Definition KS_bntbu16M : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu16M.regs0 Pbntbu16M.regs_out0).
Lemma KS_bntbu16M_ok : BG.kept_ok 80 Pbntbu16M.regs0 Pbntbu16M.regs_out0 KS_bntbu16M = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu16M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> 4096 <= (V 36%nat) <= 140737488355326 ->
  90 <= ((V 2%nat) - (V 36%nat)) <= 90 -> L5.u8_at RSEGS M ((V 36%nat) + 1) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 47%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 47%nat)) ->
  ((((V 47%nat) / 8) + 2147450880) + 8 <= (V 36%nat) \/ (V 36%nat) + 2 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 48%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 91) <= bv_unsigned a < ((V 2%nat) - 91) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 91) <= i < ((V 2%nat) - 91) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1cfc M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbu16M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 728316
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 91)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 pvzI13 pvzI14 K21 pvzI15 K23 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 36%nat => vz_36 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbu16M.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu16M.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu16M.kn0).
  { unfold know_ok, Pbntbu16M.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r HV36l HV36r K19l K19r K23 K24 K25) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu16M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu16M.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 91) <= bv_unsigned a < (vz_2 - 91) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbu16M.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu16M.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbu16M.ps0) with (map (fun i => (i, nth i Pbntbu16M.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu16M.ps0) with Pbntbu16M.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu16M.regs0 Pbntbu16M.regs_out0 80 KS_bntbu16M KS_bntbu16M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu16M.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16M.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16M.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16M.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbu16L := BndP_Eb_025S9.LibSegEb_bntbu16L.
Definition KS_bntbu16L : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu16L.regs0 Pbntbu16L.regs_out0).
Lemma KS_bntbu16L_ok : BG.kept_ok 80 Pbntbu16L.regs0 Pbntbu16L.regs_out0 KS_bntbu16L = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu16L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 2%nat) - 128) + 39) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1cfc M) (st fx' R' 0xb1d9c M')
        /\ (forall x, In x KS_bntbu16L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV73l; move HV73l before pvzI17; pose proof (proj2 pvzI17) as HV73r; move HV73r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV74l; move HV74l before pvzI18; pose proof (proj2 pvzI18) as HV74r; move HV74r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pbntbu16L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu16L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu16L.kn0).
  { unfold know_ok, Pbntbu16L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu16L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu16L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbu16L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu16L.ps0) with 0xb1d9c in Hms. change (SR.ps_regs Pbntbu16L.ps0) with (map (fun i => (i, nth i Pbntbu16L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu16L.ps0) with Pbntbu16L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu16L.regs0 Pbntbu16L.regs_out0 80 KS_bntbu16L KS_bntbu16L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu16L.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbu16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module Pbntbu32A := BndP_Eb_025S9.LibSegEb_bntbu32A.
Definition KS_bntbu32A : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu32A.regs0 Pbntbu32A.regs_out0).
Lemma KS_bntbu32A_ok : BG.kept_ok 80 Pbntbu32A.regs0 Pbntbu32A.regs_out0 KS_bntbu32A = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu32A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1da4 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bntbu32A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 728592
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pbntbu32A.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu32A.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu32A.kn0).
  { unfold know_ok, Pbntbu32A.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu32A.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu32A.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pbntbu32A.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu32A.ps0) with 0x5ec3c in Hms. change (SR.ps_regs Pbntbu32A.ps0) with (map (fun i => (i, nth i Pbntbu32A.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu32A.ps0) with Pbntbu32A.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu32A.regs0 Pbntbu32A.regs_out0 80 KS_bntbu32A KS_bntbu32A_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbu32A.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pbntbu32B := BndP_Eb_026S9.LibSegEb_bntbu32B.
Definition KS_bntbu32B : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu32B.regs0 Pbntbu32B.regs_out0).
Lemma KS_bntbu32B_ok : BG.kept_ok 80 Pbntbu32B.regs0 Pbntbu32B.regs_out0 KS_bntbu32B = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu32B_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1e10 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbu32B -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 728828
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 93)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 92)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G19 G20 G21 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 33%nat => Z_to_bv 64 vz_33 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 33%nat => vz_33 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbu32B.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu32B.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu32B.kn0).
  { unfold know_ok, Pbntbu32B.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu32B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu32B.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pbntbu32B.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu32B.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbu32B.ps0) with (map (fun i => (i, nth i Pbntbu32B.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu32B.ps0) with Pbntbu32B.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu32B.regs0 Pbntbu32B.regs_out0 80 KS_bntbu32B KS_bntbu32B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32B.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbu32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbu32M := BndP_Eb_026S9.LibSegEb_bntbu32M.
Definition KS_bntbu32M : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu32M.regs0 Pbntbu32M.regs_out0).
Lemma KS_bntbu32M_ok : BG.kept_ok 80 Pbntbu32M.regs0 Pbntbu32M.regs_out0 KS_bntbu32M = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu32M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> 4096 <= (V 36%nat) <= 140737488355326 ->
  90 <= ((V 2%nat) - (V 36%nat)) <= 92 -> L5.u8_at RSEGS M ((V 36%nat) + 1) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 47%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 47%nat)) ->
  ((((V 47%nat) / 8) + 2147450880) + 8 <= (V 36%nat) \/ (V 36%nat) + 2 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 48%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 93) <= bv_unsigned a < ((V 2%nat) - 93) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 93) <= i < ((V 2%nat) - 93) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1efc M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbu32M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 728828
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 93)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 pvzI13 pvzI14 K21 pvzI15 K23 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 36%nat => vz_36 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbu32M.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu32M.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu32M.kn0).
  { unfold know_ok, Pbntbu32M.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r HV36l HV36r K19l K19r K23 K24 K25) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu32M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu32M.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 93) <= bv_unsigned a < (vz_2 - 93) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbu32M.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu32M.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbu32M.ps0) with (map (fun i => (i, nth i Pbntbu32M.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu32M.ps0) with Pbntbu32M.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu32M.regs0 Pbntbu32M.regs_out0 80 KS_bntbu32M KS_bntbu32M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu32M.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32M.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32M.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32M.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbu32L := BndP_Eb_026S9.LibSegEb_bntbu32L.
Definition KS_bntbu32L : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu32L.regs0 Pbntbu32L.regs_out0).
Lemma KS_bntbu32L_ok : BG.kept_ok 80 Pbntbu32L.regs0 Pbntbu32L.regs_out0 KS_bntbu32L = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu32L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 2%nat) - 128) + 39) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1efc M) (st fx' R' 0xb1f9c M')
        /\ (forall x, In x KS_bntbu32L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV73l; move HV73l before pvzI17; pose proof (proj2 pvzI17) as HV73r; move HV73r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV74l; move HV74l before pvzI18; pose proof (proj2 pvzI18) as HV74r; move HV74r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pbntbu32L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu32L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu32L.kn0).
  { unfold know_ok, Pbntbu32L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu32L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu32L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbu32L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu32L.ps0) with 0xb1f9c in Hms. change (SR.ps_regs Pbntbu32L.ps0) with (map (fun i => (i, nth i Pbntbu32L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu32L.ps0) with Pbntbu32L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu32L.regs0 Pbntbu32L.regs_out0 80 KS_bntbu32L KS_bntbu32L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu32L.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbu32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module Pbntbu64A := BndP_Eb_026S9.LibSegEb_bntbu64A.
Definition KS_bntbu64A : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu64A.regs0 Pbntbu64A.regs_out0).
Lemma KS_bntbu64A_ok : BG.kept_ok 80 Pbntbu64A.regs0 Pbntbu64A.regs_out0 KS_bntbu64A = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu64A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1fa4 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bntbu64A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729104
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pbntbu64A.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu64A.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu64A.kn0).
  { unfold know_ok, Pbntbu64A.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu64A.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu64A.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pbntbu64A.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu64A.ps0) with 0x5ec3c in Hms. change (SR.ps_regs Pbntbu64A.ps0) with (map (fun i => (i, nth i Pbntbu64A.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu64A.ps0) with Pbntbu64A.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu64A.regs0 Pbntbu64A.regs_out0 80 KS_bntbu64A KS_bntbu64A_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbu64A.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pbntbu64B := BndP_Eb_026S9.LibSegEb_bntbu64B.
Definition KS_bntbu64B : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu64B.regs0 Pbntbu64B.regs_out0).
Lemma KS_bntbu64B_ok : BG.kept_ok 80 Pbntbu64B.regs0 Pbntbu64B.regs_out0 KS_bntbu64B = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu64B_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2010 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbu64B -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729392
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 97)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G19 G20 G22 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 33%nat => Z_to_bv 64 vz_33 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 33%nat => vz_33 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbu64B.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu64B.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu64B.kn0).
  { unfold know_ok, Pbntbu64B.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu64B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu64B.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pbntbu64B.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu64B.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbu64B.ps0) with (map (fun i => (i, nth i Pbntbu64B.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu64B.ps0) with Pbntbu64B.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu64B.regs0 Pbntbu64B.regs_out0 80 KS_bntbu64B KS_bntbu64B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64B.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbu64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbu64M := BndP_Eb_026S9.LibSegEb_bntbu64M.
Definition KS_bntbu64M : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu64M.regs0 Pbntbu64M.regs_out0).
Lemma KS_bntbu64M_ok : BG.kept_ok 80 Pbntbu64M.regs0 Pbntbu64M.regs_out0 KS_bntbu64M = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu64M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> 4096 <= (V 36%nat) <= 140737488355326 ->
  90 <= ((V 2%nat) - (V 36%nat)) <= 96 -> L5.u8_at RSEGS M ((V 36%nat) + 1) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 47%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 47%nat)) ->
  ((((V 47%nat) / 8) + 2147450880) + 8 <= (V 36%nat) \/ (V 36%nat) + 2 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 48%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 97) <= bv_unsigned a < ((V 2%nat) - 97) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 97) <= i < ((V 2%nat) - 97) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2130 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbu64M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729392
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 97)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 pvzI13 pvzI14 K21 pvzI15 K23 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 36%nat => vz_36 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbu64M.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu64M.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu64M.kn0).
  { unfold know_ok, Pbntbu64M.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r HV36l HV36r K19l K19r K23 K24 K25) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu64M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu64M.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 97) <= bv_unsigned a < (vz_2 - 97) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbu64M.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu64M.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbu64M.ps0) with (map (fun i => (i, nth i Pbntbu64M.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu64M.ps0) with Pbntbu64M.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu64M.regs0 Pbntbu64M.regs_out0 80 KS_bntbu64M KS_bntbu64M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu64M.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64M.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64M.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbu64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64M.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbu64L := BndP_Eb_026S9.LibSegEb_bntbu64L.
Definition KS_bntbu64L : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbu64L.regs0 Pbntbu64L.regs_out0).
Lemma KS_bntbu64L_ok : BG.kept_ok 80 Pbntbu64L.regs0 Pbntbu64L.regs_out0 KS_bntbu64L = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbu64L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 2%nat) - 128) + 39) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2130 M) (st fx' R' 0xb21d0 M')
        /\ (forall x, In x KS_bntbu64L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV73l; move HV73l before pvzI17; pose proof (proj2 pvzI17) as HV73r; move HV73r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV74l; move HV74l before pvzI18; pose proof (proj2 pvzI18) as HV74r; move HV74r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pbntbu64L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbu64L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbu64L.kn0).
  { unfold know_ok, Pbntbu64L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbu64L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbu64L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbu64L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbu64L.ps0) with 0xb21d0 in Hms. change (SR.ps_regs Pbntbu64L.ps0) with (map (fun i => (i, nth i Pbntbu64L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbu64L.ps0) with Pbntbu64L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbu64L.regs0 Pbntbu64L.regs_out0 80 KS_bntbu64L KS_bntbu64L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbu64L.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbu64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module Pbntbi16A := BndP_Eb_024S9.LibSegEb_bntbi16A.
Definition KS_bntbi16A : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi16A.regs0 Pbntbi16A.regs_out0).
Lemma KS_bntbi16A_ok : BG.kept_ok 80 Pbntbi16A.regs0 Pbntbi16A.regs_out0 KS_bntbi16A = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi16A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3614 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bntbi16A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734848
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pbntbi16A.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi16A.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi16A.kn0).
  { unfold know_ok, Pbntbi16A.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi16A.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi16A.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pbntbi16A.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi16A.ps0) with 0x5ec3c in Hms. change (SR.ps_regs Pbntbi16A.ps0) with (map (fun i => (i, nth i Pbntbi16A.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi16A.ps0) with Pbntbi16A.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi16A.regs0 Pbntbi16A.regs_out0 80 KS_bntbi16A KS_bntbi16A_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbi16A.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi16A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pbntbi16B := BndP_Eb_024S9.LibSegEb_bntbi16B.
Definition KS_bntbi16B : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi16B.regs0 Pbntbi16B.regs_out0).
Lemma KS_bntbi16B_ok : BG.kept_ok 80 Pbntbi16B.regs0 Pbntbi16B.regs_out0 KS_bntbi16B = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi16B_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3680 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbi16B -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735056
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 91)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 90)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G19 G20 G21 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 33%nat => Z_to_bv 64 vz_33 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 33%nat => vz_33 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbi16B.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi16B.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi16B.kn0).
  { unfold know_ok, Pbntbi16B.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi16B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi16B.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pbntbi16B.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi16B.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbi16B.ps0) with (map (fun i => (i, nth i Pbntbi16B.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi16B.ps0) with Pbntbi16B.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi16B.regs0 Pbntbi16B.regs_out0 80 KS_bntbi16B KS_bntbi16B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16B.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbi16B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbi16M := BndP_Eb_025S9.LibSegEb_bntbi16M.
Definition KS_bntbi16M : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi16M.regs0 Pbntbi16M.regs_out0).
Lemma KS_bntbi16M_ok : BG.kept_ok 80 Pbntbi16M.regs0 Pbntbi16M.regs_out0 KS_bntbi16M = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi16M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> 4096 <= (V 36%nat) <= 140737488355326 ->
  90 <= ((V 2%nat) - (V 36%nat)) <= 90 -> L5.u8_at RSEGS M ((V 36%nat) + 1) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 47%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 47%nat)) ->
  ((((V 47%nat) / 8) + 2147450880) + 8 <= (V 36%nat) \/ (V 36%nat) + 2 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 48%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 91) <= bv_unsigned a < ((V 2%nat) - 91) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 91) <= i < ((V 2%nat) - 91) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3750 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbi16M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735056
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 91)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 pvzI13 pvzI14 K21 pvzI15 K23 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 36%nat => vz_36 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbi16M.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi16M.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi16M.kn0).
  { unfold know_ok, Pbntbi16M.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r HV36l HV36r K19l K19r K23 K24 K25) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi16M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi16M.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 91) <= bv_unsigned a < (vz_2 - 91) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbi16M.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi16M.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbi16M.ps0) with (map (fun i => (i, nth i Pbntbi16M.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi16M.ps0) with Pbntbi16M.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi16M.regs0 Pbntbi16M.regs_out0 80 KS_bntbi16M KS_bntbi16M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi16M.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16M.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16M.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16M.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi16M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbi16L := BndP_Eb_024S9.LibSegEb_bntbi16L.
Definition KS_bntbi16L : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi16L.regs0 Pbntbi16L.regs_out0).
Lemma KS_bntbi16L_ok : BG.kept_ok 80 Pbntbi16L.regs0 Pbntbi16L.regs_out0 KS_bntbi16L = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi16L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 2%nat) - 128) + 39) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3750 M) (st fx' R' 0xb37f0 M')
        /\ (forall x, In x KS_bntbi16L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV73l; move HV73l before pvzI17; pose proof (proj2 pvzI17) as HV73r; move HV73r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV74l; move HV74l before pvzI18; pose proof (proj2 pvzI18) as HV74r; move HV74r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pbntbi16L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi16L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi16L.kn0).
  { unfold know_ok, Pbntbi16L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi16L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi16L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbi16L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi16L.ps0) with 0xb37f0 in Hms. change (SR.ps_regs Pbntbi16L.ps0) with (map (fun i => (i, nth i Pbntbi16L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi16L.ps0) with Pbntbi16L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi16L.regs0 Pbntbi16L.regs_out0 80 KS_bntbi16L KS_bntbi16L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi16L.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbi16L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module Pbntbi32A := BndP_Eb_025S9.LibSegEb_bntbi32A.
Definition KS_bntbi32A : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi32A.regs0 Pbntbi32A.regs_out0).
Lemma KS_bntbi32A_ok : BG.kept_ok 80 Pbntbi32A.regs0 Pbntbi32A.regs_out0 KS_bntbi32A = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi32A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb37f8 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bntbi32A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735332
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pbntbi32A.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi32A.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi32A.kn0).
  { unfold know_ok, Pbntbi32A.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi32A.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi32A.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pbntbi32A.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi32A.ps0) with 0x5ec3c in Hms. change (SR.ps_regs Pbntbi32A.ps0) with (map (fun i => (i, nth i Pbntbi32A.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi32A.ps0) with Pbntbi32A.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi32A.regs0 Pbntbi32A.regs_out0 80 KS_bntbi32A KS_bntbi32A_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbi32A.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi32A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pbntbi32B := BndP_Eb_025S9.LibSegEb_bntbi32B.
Definition KS_bntbi32B : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi32B.regs0 Pbntbi32B.regs_out0).
Lemma KS_bntbi32B_ok : BG.kept_ok 80 Pbntbi32B.regs0 Pbntbi32B.regs_out0 KS_bntbi32B = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi32B_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3864 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbi32B -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735568
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 93)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 92)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G19 G20 G21 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 33%nat => Z_to_bv 64 vz_33 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 33%nat => vz_33 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbi32B.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi32B.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi32B.kn0).
  { unfold know_ok, Pbntbi32B.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi32B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi32B.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pbntbi32B.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi32B.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbi32B.ps0) with (map (fun i => (i, nth i Pbntbi32B.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi32B.ps0) with Pbntbi32B.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi32B.regs0 Pbntbi32B.regs_out0 80 KS_bntbi32B KS_bntbi32B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32B.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbi32B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbi32M := BndP_Eb_025S9.LibSegEb_bntbi32M.
Definition KS_bntbi32M : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi32M.regs0 Pbntbi32M.regs_out0).
Lemma KS_bntbi32M_ok : BG.kept_ok 80 Pbntbi32M.regs0 Pbntbi32M.regs_out0 KS_bntbi32M = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi32M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> 4096 <= (V 36%nat) <= 140737488355326 ->
  90 <= ((V 2%nat) - (V 36%nat)) <= 92 -> L5.u8_at RSEGS M ((V 36%nat) + 1) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 47%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 47%nat)) ->
  ((((V 47%nat) / 8) + 2147450880) + 8 <= (V 36%nat) \/ (V 36%nat) + 2 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 48%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 93) <= bv_unsigned a < ((V 2%nat) - 93) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 93) <= i < ((V 2%nat) - 93) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3950 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbi32M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735568
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 93)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 pvzI13 pvzI14 K21 pvzI15 K23 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 36%nat => vz_36 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbi32M.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi32M.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi32M.kn0).
  { unfold know_ok, Pbntbi32M.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r HV36l HV36r K19l K19r K23 K24 K25) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi32M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi32M.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 93) <= bv_unsigned a < (vz_2 - 93) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbi32M.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi32M.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbi32M.ps0) with (map (fun i => (i, nth i Pbntbi32M.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi32M.ps0) with Pbntbi32M.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi32M.regs0 Pbntbi32M.regs_out0 80 KS_bntbi32M KS_bntbi32M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi32M.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32M.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32M.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32M.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi32M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbi32L := BndP_Eb_025S9.LibSegEb_bntbi32L.
Definition KS_bntbi32L : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi32L.regs0 Pbntbi32L.regs_out0).
Lemma KS_bntbi32L_ok : BG.kept_ok 80 Pbntbi32L.regs0 Pbntbi32L.regs_out0 KS_bntbi32L = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi32L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 47%nat) -> getr R (reg 24) = Z_to_bv 64 (((V 2%nat) - 128) + 39) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3950 M) (st fx' R' 0xb39f0 M')
        /\ (forall x, In x KS_bntbi32L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV73l; move HV73l before pvzI17; pose proof (proj2 pvzI17) as HV73r; move HV73r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV74l; move HV74l before pvzI18; pose proof (proj2 pvzI18) as HV74r; move HV74r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pbntbi32L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi32L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi32L.kn0).
  { unfold know_ok, Pbntbi32L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi32L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi32L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbi32L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi32L.ps0) with 0xb39f0 in Hms. change (SR.ps_regs Pbntbi32L.ps0) with (map (fun i => (i, nth i Pbntbi32L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi32L.ps0) with Pbntbi32L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi32L.regs0 Pbntbi32L.regs_out0 80 KS_bntbi32L KS_bntbi32L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi32L.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbi32L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module Pbntbi64A := BndP_Eb_025S9.LibSegEb_bntbi64A.
Definition KS_bntbi64A : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi64A.regs0 Pbntbi64A.regs_out0).
Lemma KS_bntbi64A_ok : BG.kept_ok 80 Pbntbi64A.regs0 Pbntbi64A.regs_out0 KS_bntbi64A = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi64A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb39f8 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bntbi64A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735844
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E Pbntbi64A.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi64A.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi64A.kn0).
  { unfold know_ok, Pbntbi64A.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi64A.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi64A.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pbntbi64A.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi64A.ps0) with 0x5ec3c in Hms. change (SR.ps_regs Pbntbi64A.ps0) with (map (fun i => (i, nth i Pbntbi64A.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi64A.ps0) with Pbntbi64A.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi64A.regs0 Pbntbi64A.regs_out0 80 KS_bntbi64A KS_bntbi64A_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg Pbntbi64A.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi64A.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pbntbi64B := BndP_Eb_025S9.LibSegEb_bntbi64B.
Definition KS_bntbi64B : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi64B.regs0 Pbntbi64B.regs_out0).
Lemma KS_bntbi64B_ok : BG.kept_ok 80 Pbntbi64B.regs0 Pbntbi64B.regs_out0 KS_bntbi64B = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi64B_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3a64 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbi64B -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 736132
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 97)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G19 G20 G22 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 33%nat => Z_to_bv 64 vz_33 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 33%nat => vz_33 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbi64B.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi64B.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi64B.kn0).
  { unfold know_ok, Pbntbi64B.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | clear - HV2l HV2r K3l K3r K18 K19; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | clear - HV47l HV47r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | clear - HV48l HV48r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi64B.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi64B.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 24) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pbntbi64B.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi64B.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbi64B.ps0) with (map (fun i => (i, nth i Pbntbi64B.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi64B.ps0) with Pbntbi64B.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi64B.regs0 Pbntbi64B.regs_out0 80 KS_bntbi64B KS_bntbi64B_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64B.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbi64B.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbi64M := BndP_Eb_025S9.LibSegEb_bntbi64M.
Definition KS_bntbi64M : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi64M.regs0 Pbntbi64M.regs_out0).
Lemma KS_bntbi64M_ok : BG.kept_ok 80 Pbntbi64M.regs0 Pbntbi64M.regs_out0 KS_bntbi64M = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi64M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> 4096 <= (V 36%nat) <= 140737488355326 ->
  90 <= ((V 2%nat) - (V 36%nat)) <= 96 -> L5.u8_at RSEGS M ((V 36%nat) + 1) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 47%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 47%nat)) ->
  ((((V 47%nat) / 8) + 2147450880) + 8 <= (V 36%nat) \/ (V 36%nat) + 2 <= (((V 47%nat) / 8) + 2147450880)) -> ((V 48%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 2 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 97) <= bv_unsigned a < ((V 2%nat) - 97) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 97) <= i < ((V 2%nat) - 97) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3b84 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bntbi64M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 736132
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 97)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 11%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 pvzI13 pvzI14 K21 pvzI15 K23 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 36%nat => vz_36 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E Pbntbi64M.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi64M.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi64M.kn0).
  { unfold know_ok, Pbntbi64M.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K25; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r HV36l HV36r K19l K19r K23 K24 K25) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K19l K19r K20l K20r K23 K24 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi64M.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi64M.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 97) <= bv_unsigned a < (vz_2 - 97) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbi64M.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18 K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi64M.ps0) with 0xb2794 in Hms. change (SR.ps_regs Pbntbi64M.ps0) with (map (fun i => (i, nth i Pbntbi64M.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi64M.ps0) with Pbntbi64M.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi64M.regs0 Pbntbi64M.regs_out0 80 KS_bntbi64M KS_bntbi64M_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi64M.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64M.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64M.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pbntbi64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64M.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi64M.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear - HV11l HV11r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K23 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module Pbntbi64L := BndP_Eb_025S9.LibSegEb_bntbi64L.
Definition KS_bntbi64L : list nat := Eval vm_compute in (BG.kept_list 80 Pbntbi64L.regs0 Pbntbi64L.regs_out0).
Lemma KS_bntbi64L_ok : BG.kept_ok 80 Pbntbi64L.regs0 Pbntbi64L.regs_out0 KS_bntbi64L = true. Proof. vm_compute. reflexivity. Qed.
Lemma bntbi64L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 11%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 47%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 2%nat) - 128) + 39) -> getr R (reg 25) = Z_to_bv 64 (((V 2%nat) - 128) + 40) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3b84 M) (st fx' R' 0xb3c24 M')
        /\ (forall x, In x KS_bntbi64L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G24 G25 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV11l; move HV11l before pvzI2; pose proof (proj2 pvzI2) as HV11r; move HV11r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV47l; move HV47l before pvzI3; pose proof (proj2 pvzI3) as HV47r; move HV47r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV73l; move HV73l before pvzI17; pose proof (proj2 pvzI17) as HV73r; move HV73r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV74l; move HV74l before pvzI18; pose proof (proj2 pvzI18) as HV74r; move HV74r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pbntbi64L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pbntbi64L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pbntbi64L.kn0).
  { unfold know_ok, Pbntbi64L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | clear - HV47l HV47r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | clear - HV48l HV48r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pbntbi64L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pbntbi64L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pbntbi64L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pbntbi64L.ps0) with 0xb3c24 in Hms. change (SR.ps_regs Pbntbi64L.ps0) with (map (fun i => (i, nth i Pbntbi64L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pbntbi64L.ps0) with Pbntbi64L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pbntbi64L.regs0 Pbntbi64L.regs_out0 80 KS_bntbi64L KS_bntbi64L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pbntbi64L.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pbntbi64L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

End PEBENTBP.
