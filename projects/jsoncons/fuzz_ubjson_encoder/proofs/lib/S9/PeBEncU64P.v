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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_082S9 BndP_Eb_083S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENCVUP.
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

Module PbvuA := BndP_Eb_082S9.LibSegEb_bvuA.
Definition KS_bvuA : list nat := Eval vm_compute in (BG.kept_list 80 PbvuA.regs0 PbvuA.regs_out0).
Lemma KS_bvuA_ok : BG.kept_ok 80 PbvuA.regs0 PbvuA.regs_out0 KS_bvuA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac028 M) (st fx' R' 0x5ec3c M')
        /\ (forall x, In x KS_bvuA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 704660
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 10)
        /\ getr R' (reg 20) = getr R (reg 11)
        /\ getr R' (reg 23) = Z_to_bv 64 2147450880
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
  assert (HR: regs_ok E PbvuA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuA.kn0).
  { unfold know_ok, PbvuA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbvuA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuA.ps0) with 0x5ec3c in Hms. change (SR.ps_regs PbvuA.ps0) with (map (fun i => (i, nth i PbvuA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuA.ps0) with PbvuA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuA.regs0 PbvuA.regs_out0 80 KS_bvuA KS_bvuA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbvuA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvuA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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

Module PbvuD8 := BndP_Eb_083S9.LibSegEb_bvuD8.
Definition KS_bvuD8 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuD8.regs0 PbvuD8.regs_out0).
Lemma KS_bvuD8_ok : BG.kept_ok 80 PbvuD8.regs0 PbvuD8.regs_out0 KS_bvuD8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuD8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 11%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac094 M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bvuD8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 704952
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 93)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G23 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuD8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuD8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuD8.kn0).
  { unfold know_ok, PbvuD8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuD8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuD8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvuD8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuD8.ps0) with 0xb120c in Hms. change (SR.ps_regs PbvuD8.ps0) with (map (fun i => (i, nth i PbvuD8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuD8.ps0) with PbvuD8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuD8.regs0 PbvuD8.regs_out0 80 KS_bvuD8 KS_bvuD8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD8.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuD8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvuD16 := BndP_Eb_082S9.LibSegEb_bvuD16.
Definition KS_bvuD16 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuD16.regs0 PbvuD16.regs_out0).
Lemma KS_bvuD16_ok : BG.kept_ok 80 PbvuD16.regs0 PbvuD16.regs_out0 KS_bvuD16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuD16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 256 <= (V 11%nat) <= 32767 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac094 M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bvuD16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705040
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 91)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G23 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuD16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuD16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuD16.kn0).
  { unfold know_ok, PbvuD16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuD16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuD16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvuD16.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuD16.ps0) with 0xb120c in Hms. change (SR.ps_regs PbvuD16.ps0) with (map (fun i => (i, nth i PbvuD16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuD16.ps0) with PbvuD16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuD16.regs0 PbvuD16.regs_out0 80 KS_bvuD16 KS_bvuD16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD16.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuD16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvuD32 := BndP_Eb_082S9.LibSegEb_bvuD32.
Definition KS_bvuD32 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuD32.regs0 PbvuD32.regs_out0).
Lemma KS_bvuD32_ok : BG.kept_ok 80 PbvuD32.regs0 PbvuD32.regs_out0 KS_bvuD32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuD32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 32768 <= (V 11%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac094 M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bvuD32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705112
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 90)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G23 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuD32.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuD32.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuD32.kn0).
  { unfold know_ok, PbvuD32.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuD32.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuD32.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvuD32.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuD32.ps0) with 0xb120c in Hms. change (SR.ps_regs PbvuD32.ps0) with (map (fun i => (i, nth i PbvuD32.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuD32.ps0) with PbvuD32.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuD32.regs0 PbvuD32.regs_out0 80 KS_bvuD32 KS_bvuD32_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD32.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuD32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvuD64 := BndP_Eb_082S9.LibSegEb_bvuD64.
Definition KS_bvuD64 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuD64.regs0 PbvuD64.regs_out0).
Lemma KS_bvuD64_ok : BG.kept_ok 80 PbvuD64.regs0 PbvuD64.regs_out0 KS_bvuD64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuD64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 2147483648 <= (V 11%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 40) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac094 M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bvuD64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 704880
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 89)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G19 G20 G23 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI13 K34 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K33l; move K33l before pvzI13; pose proof (proj2 pvzI13) as K33r; move K33r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuD64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuD64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuD64.kn0).
  { unfold know_ok, PbvuD64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | clear - HV2l HV2r K3l K3r K18 K19 K28; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28) | evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | clear - HV10l HV10r K20 K21 K22 K23l K23r K25 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K33l K33r) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuD64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuD64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 40) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvuD64.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K18 K19 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K18 K19 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuD64.ps0) with 0xb120c in Hms. change (SR.ps_regs PbvuD64.ps0) with (map (fun i => (i, nth i PbvuD64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuD64.ps0) with PbvuD64.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuD64.regs0 PbvuD64.regs_out0 80 KS_bvuD64 KS_bvuD64_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuD64.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuD64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K17 K18 K20 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvuP8 := BndP_Eb_083S9.LibSegEb_bvuP8.
Definition KS_bvuP8 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuP8.regs0 PbvuP8.regs_out0).
Lemma KS_bvuP8_ok : BG.kept_ok 80 PbvuP8.regs0 PbvuP8.regs_out0 KS_bvuP8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuP8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  0 <= (V 11%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 92) <= bv_unsigned a < ((V 2%nat) - 92) + 1) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 92) <= i < ((V 2%nat) - 92) + 1) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac1b8 M) (st fx' R' 0xb2794 M')
        /\ (forall x, In x KS_bvuP8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 704976
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 92)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) ((V 10%nat) + 8)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21 pvzI12 K23 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K22l; move K22l before pvzI12; pose proof (proj2 pvzI12) as K22r; move K22r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K24l; move K24l before pvzI13; pose proof (proj2 pvzI13) as K24r; move K24r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuP8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuP8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuP8.kn0).
  { unfold know_ok, PbvuP8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuP8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuP8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 92) <= bv_unsigned a < (vz_2 - 92) + 1) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvuP8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuP8.ps0) with 0xb2794 in Hms. change (SR.ps_regs PbvuP8.ps0) with (map (fun i => (i, nth i PbvuP8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuP8.ps0) with PbvuP8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuP8.regs0 PbvuP8.regs_out0 80 KS_bvuP8 KS_bvuP8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuP8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuP8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuP8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuP8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuP8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuP8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbvuW16 := BndP_Eb_083S9.LibSegEb_bvuW16.
Definition KS_bvuW16 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuW16.regs0 PbvuW16.regs_out0).
Lemma KS_bvuW16_ok : BG.kept_ok 80 PbvuW16.regs0 PbvuW16.regs_out0 KS_bvuW16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuW16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  256 <= (V 11%nat) <= 32767 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac210 M) (st fx' R' 0xb3614 M')
        /\ (forall x, In x KS_bvuW16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705056
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuW16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuW16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuW16.kn0).
  { unfold know_ok, PbvuW16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuW16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuW16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvuW16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuW16.ps0) with 0xb3614 in Hms. change (SR.ps_regs PbvuW16.ps0) with (map (fun i => (i, nth i PbvuW16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuW16.ps0) with PbvuW16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuW16.regs0 PbvuW16.regs_out0 80 KS_bvuW16 KS_bvuW16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuW16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuW16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvuW16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuW16.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvuW32 := BndP_Eb_083S9.LibSegEb_bvuW32.
Definition KS_bvuW32 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuW32.regs0 PbvuW32.regs_out0).
Lemma KS_bvuW32_ok : BG.kept_ok 80 PbvuW32.regs0 PbvuW32.regs_out0 KS_bvuW32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuW32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  32768 <= (V 11%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac258 M) (st fx' R' 0xb37f8 M')
        /\ (forall x, In x KS_bvuW32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705124
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuW32.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuW32.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuW32.kn0).
  { unfold know_ok, PbvuW32.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuW32.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuW32.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvuW32.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuW32.ps0) with 0xb37f8 in Hms. change (SR.ps_regs PbvuW32.ps0) with (map (fun i => (i, nth i PbvuW32.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuW32.ps0) with PbvuW32.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuW32.regs0 PbvuW32.regs_out0 80 KS_bvuW32 KS_bvuW32_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuW32.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuW32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuW32.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuW32.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvuW32.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuW32.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvuW64 := BndP_Eb_083S9.LibSegEb_bvuW64.
Definition KS_bvuW64 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuW64.regs0 PbvuW64.regs_out0).
Lemma KS_bvuW64_ok : BG.kept_ok 80 PbvuW64.regs0 PbvuW64.regs_out0 KS_bvuW64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuW64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  2147483648 <= (V 11%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac170 M) (st fx' R' 0xb39f8 M')
        /\ (forall x, In x KS_bvuW64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 704892
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuW64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuW64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuW64.kn0).
  { unfold know_ok, PbvuW64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuW64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuW64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvuW64.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuW64.ps0) with 0xb39f8 in Hms. change (SR.ps_regs PbvuW64.ps0) with (map (fun i => (i, nth i PbvuW64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuW64.ps0) with PbvuW64.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuW64.regs0 PbvuW64.regs_out0 80 KS_bvuW64 KS_bvuW64_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuW64.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuW64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuW64.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuW64.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbvuW64.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuW64.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbvuJ8 := BndP_Eb_083S9.LibSegEb_bvuJ8.
Definition KS_bvuJ8 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuJ8.regs0 PbvuJ8.regs_out0).
Lemma KS_bvuJ8_ok : BG.kept_ok 80 PbvuJ8.regs0 PbvuJ8.regs_out0 KS_bvuJ8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuJ8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac1d0 M) (st fx' R' 0xac264 M')
        /\ (forall x, In x KS_bvuJ8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21 pvzI12 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K22l; move K22l before pvzI12; pose proof (proj2 pvzI12) as K22r; move K22r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuJ8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuJ8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuJ8.kn0).
  { unfold know_ok, PbvuJ8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | clear - HV2l HV2r K3l K3r K17 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r) | clear; lia | exact K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuJ8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuJ8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbvuJ8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuJ8.ps0) with 0xac264 in Hms. change (SR.ps_regs PbvuJ8.ps0) with (map (fun i => (i, nth i PbvuJ8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuJ8.ps0) with PbvuJ8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuJ8.regs0 PbvuJ8.regs_out0 80 KS_bvuJ8 KS_bvuJ8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuJ8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuJ8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvuJ16 := BndP_Eb_083S9.LibSegEb_bvuJ16.
Definition KS_bvuJ16 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuJ16.regs0 PbvuJ16.regs_out0).
Lemma KS_bvuJ16_ok : BG.kept_ok 80 PbvuJ16.regs0 PbvuJ16.regs_out0 KS_bvuJ16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac220 M) (st fx' R' 0xac264 M')
        /\ (forall x, In x KS_bvuJ16 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuJ16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuJ16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuJ16.kn0).
  { unfold know_ok, PbvuJ16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuJ16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuJ16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvuJ16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuJ16.ps0) with 0xac264 in Hms. change (SR.ps_regs PbvuJ16.ps0) with (map (fun i => (i, nth i PbvuJ16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuJ16.ps0) with PbvuJ16.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbvuJ16.regs0 PbvuJ16.regs_out0 80 KS_bvuJ16 KS_bvuJ16_ok HR Hag Hregs j Hj).
Qed.

Module PbvuJ64 := BndP_Eb_083S9.LibSegEb_bvuJ64.
Definition KS_bvuJ64 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuJ64.regs0 PbvuJ64.regs_out0).
Lemma KS_bvuJ64_ok : BG.kept_ok 80 PbvuJ64.regs0 PbvuJ64.regs_out0 KS_bvuJ64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuJ64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac17c M) (st fx' R' 0xac264 M')
        /\ (forall x, In x KS_bvuJ64 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbvuJ64.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuJ64.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuJ64.kn0).
  { unfold know_ok, PbvuJ64.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuJ64.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuJ64.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbvuJ64.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuJ64.ps0) with 0xac264 in Hms. change (SR.ps_regs PbvuJ64.ps0) with (map (fun i => (i, nth i PbvuJ64.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuJ64.ps0) with PbvuJ64.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbvuJ64.regs0 PbvuJ64.regs_out0 80 KS_bvuJ64 KS_bvuJ64_ok HR Hag Hregs j Hj).
Qed.

Module PbvuE0 := BndP_Eb_083S9.LibSegEb_bvuE0.
Definition KS_bvuE0 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuE0.regs0 PbvuE0.regs_out0).
Lemma KS_bvuE0_ok : BG.kept_ok 80 PbvuE0.regs0 PbvuE0.regs_out0 KS_bvuE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) -> 0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac264 M) (st fx' R' 0xac368 M')
        /\ (forall x, In x KS_bvuE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 pvzI23 K14 K15 K16 K17 K18 K19 K20 K21 pvzI24 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI25 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV69l; move HV69l before pvzI15; pose proof (proj2 pvzI15) as HV69r; move HV69r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV70l; move HV70l before pvzI16; pose proof (proj2 pvzI16) as HV70r; move HV70r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV73l; move HV73l before pvzI19; pose proof (proj2 pvzI19) as HV73r; move HV73r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV74l; move HV74l before pvzI20; pose proof (proj2 pvzI20) as HV74r; move HV74r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K13l; move K13l before pvzI23; pose proof (proj2 pvzI23) as K13r; move K13r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K22l; move K22l before pvzI24; pose proof (proj2 pvzI24) as K22r; move K22r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PbvuE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuE0.kn0).
  { unfold know_ok, PbvuE0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | clear - HV2l HV2r K3l K3r K17 K18 K27; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuE0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbvuE0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuE0.ps0) with 0xac368 in Hms. change (SR.ps_regs PbvuE0.ps0) with (map (fun i => (i, nth i PbvuE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuE0.ps0) with PbvuE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuE0.regs0 PbvuE0.regs_out0 80 KS_bvuE0 KS_bvuE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.

Module PbvuE1 := BndP_Eb_083S9.LibSegEb_bvuE1.
Definition KS_bvuE1 : list nat := Eval vm_compute in (BG.kept_list 80 PbvuE1.regs0 PbvuE1.regs_out0).
Lemma KS_bvuE1_ok : BG.kept_ok 80 PbvuE1.regs0 PbvuE1.regs_out0 KS_bvuE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac264 M) (st fx' R' 0xac368 M')
        /\ (forall x, In x KS_bvuE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI23 K4 K5 pvzI24 K7 K8 K9 K10 K11 K12 pvzI25 K14 K15 K16 K17 K18 K19 K20 K21 pvzI26 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI27 pvzI28 K35 pvzI29 K37 K38 K39 K40 K41 K42 K43 K44 K45 pvzI30 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV69l; move HV69l before pvzI17; pose proof (proj2 pvzI17) as HV69r; move HV69r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV71l; move HV71l before pvzI19; pose proof (proj2 pvzI19) as HV71r; move HV71r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV72l; move HV72l before pvzI20; pose proof (proj2 pvzI20) as HV72r; move HV72r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV73l; move HV73l before pvzI21; pose proof (proj2 pvzI21) as HV73r; move HV73r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV74l; move HV74l before pvzI22; pose proof (proj2 pvzI22) as HV74r; move HV74r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K3l; move K3l before pvzI23; pose proof (proj2 pvzI23) as K3r; move K3r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K6l; move K6l before pvzI24; pose proof (proj2 pvzI24) as K6r; move K6r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K13l; move K13l before pvzI25; pose proof (proj2 pvzI25) as K13r; move K13r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K22l; move K22l before pvzI26; pose proof (proj2 pvzI26) as K22r; move K22r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K33l; move K33l before pvzI27; pose proof (proj2 pvzI27) as K33r; move K33r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K34l; move K34l before pvzI28; pose proof (proj2 pvzI28) as K34r; move K34r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K36l; move K36l before pvzI29; pose proof (proj2 pvzI29) as K36r; move K36r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K46l; move K46l before pvzI30; pose proof (proj2 pvzI30) as K46r; move K46r before pvzI30; clear pvzI30.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 38%nat => vz_38 | 39%nat => vz_39 | 42%nat => vz_42 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PbvuE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuE1.kn0).
  { unfold know_ok, PbvuE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r HV39l HV39r K34l K34r K38 K40 K41 K42 K43 K44) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear - HV42l HV42r K46l K46r) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K46l K46r) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K57]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuE1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbvuE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuE1.ps0) with 0xac368 in Hms. change (SR.ps_regs PbvuE1.ps0) with (map (fun i => (i, nth i PbvuE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuE1.ps0) with PbvuE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuE1.regs0 PbvuE1.regs_out0 80 KS_bvuE1 KS_bvuE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K46l K46r) | clear; lia].
Qed.

Module PbvuE1w := BndP_Eb_083S9.LibSegEb_bvuE1w.
Definition KS_bvuE1w : list nat := Eval vm_compute in (BG.kept_list 80 PbvuE1w.regs0 PbvuE1w.regs_out0).
Lemma KS_bvuE1w_ok : BG.kept_ok 80 PbvuE1w.regs0 PbvuE1w.regs_out0 KS_bvuE1w = true. Proof. vm_compute. reflexivity. Qed.
Lemma bvuE1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 10%nat) -> getr R (reg 20) = Z_to_bv 64 (V 11%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 64 -> L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac264 M) (st fx' R' 0xac368 M')
        /\ (forall x, In x KS_bvuE1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G23 G24 G25 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 pvzI24 K14 K15 K16 K17 K18 K19 K20 K21 pvzI25 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI26 pvzI27 K35 pvzI28 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV73l; move HV73l before pvzI20; pose proof (proj2 pvzI20) as HV73r; move HV73r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV74l; move HV74l before pvzI21; pose proof (proj2 pvzI21) as HV74r; move HV74r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K13l; move K13l before pvzI24; pose proof (proj2 pvzI24) as K13r; move K13r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K22l; move K22l before pvzI25; pose proof (proj2 pvzI25) as K22r; move K22r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K33l; move K33l before pvzI26; pose proof (proj2 pvzI26) as K33r; move K33r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K34l; move K34l before pvzI27; pose proof (proj2 pvzI27) as K34r; move K34r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K36l; move K36l before pvzI28; pose proof (proj2 pvzI28) as K36r; move K36r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E PbvuE1w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbvuE1w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbvuE1w.kn0).
  { unfold know_ok, PbvuE1w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K36l K36r HV39l HV39r K34l K34r K38 K40 K41 K42 K43 K44) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K19 K20 K21 K22l K22r K24 K27 K41) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K17 K18 K27 K40) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | clear - HV2l HV2r K3l K3r K17 K18 K27 K40; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbvuE1w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbvuE1w.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbvuE1w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbvuE1w.ps0) with 0xac368 in Hms. change (SR.ps_regs PbvuE1w.ps0) with (map (fun i => (i, nth i PbvuE1w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbvuE1w.ps0) with PbvuE1w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbvuE1w.regs0 PbvuE1w.regs_out0 80 KS_bvuE1w KS_bvuE1w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbvuE1w.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbvuE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r K15 K16 K18 K20 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r K10 K16 K17 K19 K21 K42 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K34l K34r K36l K36r K38 K40 K41 K42 K43 K44) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEBENCVUP.
