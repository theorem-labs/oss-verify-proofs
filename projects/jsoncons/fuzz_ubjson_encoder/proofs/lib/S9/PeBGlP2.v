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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_003S9 BndP_Eb_005S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBGLP2.
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

Module PaglNi := BndP_Eb_003S9.LibSegEb_aglNi.
Definition KS_aglNi : list nat := Eval vm_compute in (BG.kept_list 80 PaglNi.regs0 PaglNi.regs_out0).
Lemma KS_aglNi_ok : BG.kept_ok 80 PaglNi.regs0 PaglNi.regs_out0 KS_aglNi = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglNi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 48) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba288 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglNi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762532
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PaglNi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglNi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglNi.kn0).
  { unfold know_ok, PaglNi.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglNi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglNi.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglNi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglNi.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglNi.ps0) with (map (fun i => (i, nth i PaglNi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglNi.ps0) with PaglNi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglNi.regs0 PaglNi.regs_out0 80 KS_aglNi KS_aglNi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglNi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglNi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglNi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglNi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglNi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglNi.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglNU := BndP_Eb_003S9.LibSegEb_aglNU.
Definition KS_aglNU : list nat := Eval vm_compute in (BG.kept_list 80 PaglNU.regs0 PaglNU.regs_out0).
Lemma KS_aglNU_ok : BG.kept_ok 80 PaglNU.regs0 PaglNU.regs_out0 KS_aglNU = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglNU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 64) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba3bc M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglNU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G19 G20 G21 G22 G24 G25 G26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PaglNU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglNU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglNU.kn0).
  { unfold know_ok, PaglNU.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglNU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglNU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglNU.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglNU.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglNU.ps0) with (map (fun i => (i, nth i PaglNU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglNU.ps0) with PaglNU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglNU.regs0 PaglNU.regs_out0 80 KS_aglNU KS_aglNU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglNU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglNU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglNU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglNU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglNU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglNU.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglNI := BndP_Eb_003S9.LibSegEb_aglNI.
Definition KS_aglNI : list nat := Eval vm_compute in (BG.kept_list 80 PaglNI.regs0 PaglNI.regs_out0).
Lemma KS_aglNI_ok : BG.kept_ok 80 PaglNI.regs0 PaglNI.regs_out0 KS_aglNI = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglNI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 80) -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  0 <= (V 49%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba43c M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglNI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763500
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglNI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglNI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglNI.kn0).
  { unfold know_ok, PaglNI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglNI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglNI.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglNI.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglNI.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglNI.ps0) with (map (fun i => (i, nth i PaglNI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglNI.ps0) with PaglNI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglNI.regs0 PaglNI.regs_out0 80 KS_aglNI KS_aglNI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglNI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglNI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglNI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglNI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglNI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglNI.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglNl := BndP_Eb_003S9.LibSegEb_aglNl.
Definition KS_aglNl : list nat := Eval vm_compute in (BG.kept_list 80 PaglNl.regs0 PaglNl.regs_out0).
Lemma KS_aglNl_ok : BG.kept_ok 80 PaglNl.regs0 PaglNl.regs_out0 KS_aglNl = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglNl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  0 <= (V 49%nat) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba3e4 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglNl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763336
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglNl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglNl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglNl.kn0).
  { unfold know_ok, PaglNl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglNl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglNl.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglNl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglNl.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglNl.ps0) with (map (fun i => (i, nth i PaglNl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglNl.ps0) with PaglNl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglNl.regs0 PaglNl.regs_out0 80 KS_aglNl KS_aglNl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglNl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglNl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglNl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglNl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglNl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglNl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglNl.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglNl.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglNL := BndP_Eb_003S9.LibSegEb_aglNL.
Definition KS_aglNL : list nat := Eval vm_compute in (BG.kept_list 80 PaglNL.regs0 PaglNL.regs_out0).
Lemma KS_aglNL_ok : BG.kept_ok 80 PaglNL.regs0 PaglNL.regs_out0 KS_aglNL = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglNL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 112) -> getr R (reg 23) = Z_to_bv 64 8 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  0 <= (V 49%nat) <= 7 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba328 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglNL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763396
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglNL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglNL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglNL.kn0).
  { unfold know_ok, PaglNL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglNL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglNL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglNL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglNL.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglNL.ps0) with (map (fun i => (i, nth i PaglNL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglNL.ps0) with PaglNL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglNL.regs0 PaglNL.regs_out0 80 KS_aglNL KS_aglNL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglNL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglNL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglNL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglNL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglNL.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglSiN := BndP_Eb_003S9.LibSegEb_aglSiN.
Definition KS_aglSiN : list nat := Eval vm_compute in (BG.kept_list 80 PaglSiN.regs0 PaglSiN.regs_out0).
Lemma KS_aglSiN_ok : BG.kept_ok 80 PaglSiN.regs0 PaglSiN.regs_out0 KS_aglSiN = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSiN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 48) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  9223372036854775808 <= (V 49%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba290 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglSiN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 762532
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 22) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglSiN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSiN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSiN.kn0).
  { unfold know_ok, PaglSiN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSiN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSiN.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglSiN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSiN.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglSiN.ps0) with (map (fun i => (i, nth i PaglSiN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSiN.ps0) with PaglSiN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSiN.regs0 PaglSiN.regs_out0 80 KS_aglSiN KS_aglSiN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSiN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSiN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglSiN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSiN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglSiN.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglSiN.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglSIN := BndP_Eb_003S9.LibSegEb_aglSIN.
Definition KS_aglSIN : list nat := Eval vm_compute in (BG.kept_list 80 PaglSIN.regs0 PaglSIN.regs_out0).
Lemma KS_aglSIN_ok : BG.kept_ok 80 PaglSIN.regs0 PaglSIN.regs_out0 KS_aglSIN = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSIN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 80) -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  9223372036854775808 <= (V 49%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba450 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglSIN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763500
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglSIN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSIN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSIN.kn0).
  { unfold know_ok, PaglSIN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSIN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSIN.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglSIN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSIN.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglSIN.ps0) with (map (fun i => (i, nth i PaglSIN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSIN.ps0) with PaglSIN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSIN.regs0 PaglSIN.regs_out0 80 KS_aglSIN KS_aglSIN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSIN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSIN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglSIN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglSIN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSIN.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglSlN := BndP_Eb_003S9.LibSegEb_aglSlN.
Definition KS_aglSlN : list nat := Eval vm_compute in (BG.kept_list 80 PaglSlN.regs0 PaglSlN.regs_out0).
Lemma KS_aglSlN_ok : BG.kept_ok 80 PaglSlN.regs0 PaglSlN.regs_out0 KS_aglSlN = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSlN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  9223372036854775808 <= (V 49%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba418 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglSlN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763336
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglSlN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSlN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSlN.kn0).
  { unfold know_ok, PaglSlN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSlN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSlN.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglSlN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSlN.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglSlN.ps0) with (map (fun i => (i, nth i PaglSlN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSlN.ps0) with PaglSlN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSlN.regs0 PaglSlN.regs_out0 80 KS_aglSlN KS_aglSlN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSlN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSlN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglSlN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglSlN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSlN.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglSLN := BndP_Eb_003S9.LibSegEb_aglSLN.
Definition KS_aglSLN : list nat := Eval vm_compute in (BG.kept_list 80 PaglSLN.regs0 PaglSLN.regs_out0).
Lemma KS_aglSLN_ok : BG.kept_ok 80 PaglSLN.regs0 PaglSLN.regs_out0 KS_aglSLN = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSLN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 112) -> getr R (reg 23) = Z_to_bv 64 8 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  9223372036854775808 <= (V 49%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba394 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_aglSLN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 763396
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_49 := V 49%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 49%nat => Z_to_bv 64 vz_49 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 49%nat => vz_49 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 50%nat. }
  assert (HR: regs_ok E PaglSLN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSLN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSLN.kn0).
  { unfold know_ok, PaglSLN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSLN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSLN.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglSLN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSLN.ps0) with 0xafda8 in Hms. change (SR.ps_regs PaglSLN.ps0) with (map (fun i => (i, nth i PaglSLN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSLN.ps0) with PaglSLN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSLN.regs0 PaglSLN.regs_out0 80 KS_aglSLN KS_aglSLN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSLN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSLN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglSLN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaglSLN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSLN.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaglZTR := BndP_Eb_005S9.LibSegEb_aglZTR.
Definition KS_aglZTR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZTR.regs0 PaglZTR.regs_out0).
Lemma KS_aglZTR_ok : BG.kept_ok 80 PaglZTR.regs0 PaglZTR.regs_out0 KS_aglZTR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZTR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba2d8 M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZTR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZTR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZTR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZTR.kn0).
  { unfold know_ok, PaglZTR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZTR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZTR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZTR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZTR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZTR.ps0) with (map (fun i => (i, nth i PaglZTR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZTR.ps0) with PaglZTR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZTR.regs0 PaglZTR.regs_out0 80 KS_aglZTR KS_aglZTR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZTR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZTR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglZiR := BndP_Eb_005S9.LibSegEb_aglZiR.
Definition KS_aglZiR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZiR.regs0 PaglZiR.regs_out0).
Lemma KS_aglZiR_ok : BG.kept_ok 80 PaglZiR.regs0 PaglZiR.regs_out0 KS_aglZiR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZiR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba2a4 M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZiR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZiR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZiR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZiR.kn0).
  { unfold know_ok, PaglZiR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZiR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZiR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZiR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZiR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZiR.ps0) with (map (fun i => (i, nth i PaglZiR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZiR.ps0) with PaglZiR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZiR.regs0 PaglZiR.regs_out0 80 KS_aglZiR KS_aglZiR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZiR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZiR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglZUR := BndP_Eb_005S9.LibSegEb_aglZUR.
Definition KS_aglZUR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZUR.regs0 PaglZUR.regs_out0).
Lemma KS_aglZUR_ok : BG.kept_ok 80 PaglZUR.regs0 PaglZUR.regs_out0 KS_aglZUR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZUR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba638 M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZUR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZUR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZUR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZUR.kn0).
  { unfold know_ok, PaglZUR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZUR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZUR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZUR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZUR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZUR.ps0) with (map (fun i => (i, nth i PaglZUR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZUR.ps0) with PaglZUR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZUR.regs0 PaglZUR.regs_out0 80 KS_aglZUR KS_aglZUR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZUR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZUR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglZIR := BndP_Eb_005S9.LibSegEb_aglZIR.
Definition KS_aglZIR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZIR.regs0 PaglZIR.regs_out0).
Lemma KS_aglZIR_ok : BG.kept_ok 80 PaglZIR.regs0 PaglZIR.regs_out0 KS_aglZIR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZIR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba66c M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZIR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZIR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZIR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZIR.kn0).
  { unfold know_ok, PaglZIR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZIR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZIR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZIR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZIR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZIR.ps0) with (map (fun i => (i, nth i PaglZIR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZIR.ps0) with PaglZIR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZIR.regs0 PaglZIR.regs_out0 80 KS_aglZIR KS_aglZIR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZIR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZIR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglZlR := BndP_Eb_005S9.LibSegEb_aglZlR.
Definition KS_aglZlR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZlR.regs0 PaglZlR.regs_out0).
Lemma KS_aglZlR_ok : BG.kept_ok 80 PaglZlR.regs0 PaglZlR.regs_out0 KS_aglZlR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZlR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba5c8 M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZlR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZlR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZlR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZlR.kn0).
  { unfold know_ok, PaglZlR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZlR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZlR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZlR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZlR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZlR.ps0) with (map (fun i => (i, nth i PaglZlR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZlR.ps0) with PaglZlR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZlR.regs0 PaglZlR.regs_out0 80 KS_aglZlR KS_aglZlR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZlR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZlR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglZLR := BndP_Eb_005S9.LibSegEb_aglZLR.
Definition KS_aglZLR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZLR.regs0 PaglZLR.regs_out0).
Lemma KS_aglZLR_ok : BG.kept_ok 80 PaglZLR.regs0 PaglZLR.regs_out0 KS_aglZLR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZLR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba604 M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZLR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZLR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZLR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZLR.kn0).
  { unfold know_ok, PaglZLR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZLR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZLR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZLR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZLR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZLR.ps0) with (map (fun i => (i, nth i PaglZLR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZLR.ps0) with PaglZLR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZLR.regs0 PaglZLR.regs_out0 80 KS_aglZLR KS_aglZLR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZLR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZLR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglZDR := BndP_Eb_005S9.LibSegEb_aglZDR.
Definition KS_aglZDR : list nat := Eval vm_compute in (BG.kept_list 80 PaglZDR.regs0 PaglZDR.regs_out0).
Lemma KS_aglZDR_ok : BG.kept_ok 80 PaglZDR.regs0 PaglZDR.regs_out0 KS_aglZDR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglZDR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 ->
  L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 256 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 32 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xba468 M) (st fx' R' 0xba5b4 M')
        /\ (forall x, In x KS_aglZDR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
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
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G24 G25 G26 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 K10 pvzI20 K12 K13 K14 K15 K16 K17 pvzI21 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV64l; move HV64l before pvzI6; pose proof (proj2 pvzI6) as HV64r; move HV64r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV65l; move HV65l before pvzI7; pose proof (proj2 pvzI7) as HV65r; move HV65r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV66l; move HV66l before pvzI8; pose proof (proj2 pvzI8) as HV66r; move HV66r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV67l; move HV67l before pvzI9; pose proof (proj2 pvzI9) as HV67r; move HV67r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV68l; move HV68l before pvzI10; pose proof (proj2 pvzI10) as HV68r; move HV68r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV69l; move HV69l before pvzI11; pose proof (proj2 pvzI11) as HV69r; move HV69r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV70l; move HV70l before pvzI12; pose proof (proj2 pvzI12) as HV70r; move HV70r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV71l; move HV71l before pvzI13; pose proof (proj2 pvzI13) as HV71r; move HV71r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV72l; move HV72l before pvzI14; pose proof (proj2 pvzI14) as HV72r; move HV72r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV73l; move HV73l before pvzI15; pose proof (proj2 pvzI15) as HV73r; move HV73r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV74l; move HV74l before pvzI16; pose proof (proj2 pvzI16) as HV74r; move HV74r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV75l; move HV75l before pvzI17; pose proof (proj2 pvzI17) as HV75r; move HV75r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglZDR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglZDR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglZDR.kn0).
  { unfold know_ok, PaglZDR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | clear - HV48l HV48r K18l K18r K20 K21 K23 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K22 K23) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | clear - HV2l HV2r K0l K0r K10 K22 K23; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglZDR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglZDR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaglZDR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K18l K18r K20 K21 K23 K25 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglZDR.ps0) with 0xba5b4 in Hms. change (SR.ps_regs PaglZDR.ps0) with (map (fun i => (i, nth i PaglZDR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglZDR.ps0) with PaglZDR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglZDR.regs0 PaglZDR.regs_out0 80 KS_aglZDR KS_aglZDR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglZDR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglZDR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K18l K18r K20 K21 K23 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5 K10 K24 K25 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K11l K11r K15 K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEBGLP2.
