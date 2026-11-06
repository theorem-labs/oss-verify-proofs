(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Bo0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA .
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_tpA0 LibSegY_tpA16 LibSegY_tpB LibSegY_tpCbig LibSegY_tpC LibSegY_tpD LibSegY_tpE LibSegY_tpF LibSegY_tpHi LibSegY_tpHd LibSegY_tpH2 LibSegY_tpI.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ATP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

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
Module PtpA0 := LibSegY_tpA0.
Definition KS_tpA0 : list nat := Eval vm_compute in (BG.kept_list 64 PtpA0.regs0 PtpA0.regs_out0).
Lemma KS_tpA0_ok : BG.kept_ok 64 PtpA0.regs0 PtpA0.regs_out0 KS_tpA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e108 M) (st fx' R' 0x48f64 M')
        /\ (forall x, In x KS_tpA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582012
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 10) = Z_to_bv 64 352
        /\ getr R' (reg 11) = Z_to_bv 64 911160
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 33%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PtpA0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpA0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpA0.kn0).
  { unfold know_ok, PtpA0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtpA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpA0.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpA0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpA0.ps0) with 0x48f64 in Hms. change (SR.ps_regs PtpA0.ps0) with (map (fun i => (i, nth i PtpA0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpA0.ps0) with PtpA0.cells0 in Hcells. unfold PtpA0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpA0.regs0 PtpA0.regs_out0 64 KS_tpA0 KS_tpA0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtpA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpA16 := LibSegY_tpA16.
Definition KS_tpA16 : list nat := Eval vm_compute in (BG.kept_list 64 PtpA16.regs0 PtpA16.regs_out0).
Lemma KS_tpA16_ok : BG.kept_ok 64 PtpA16.regs0 PtpA16.regs_out0 KS_tpA16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355312 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 208 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 208) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 208) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e108 M) (st fx' R' 0x48f64 M')
        /\ (forall x, In x KS_tpA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582012
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 10) = Z_to_bv 64 352
        /\ getr R' (reg 11) = Z_to_bv 64 911160
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' (V 2%nat) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PtpA16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpA16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpA16.kn0).
  { unfold know_ok, PtpA16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtpA16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpA16.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 208) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpA16.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpA16.ps0) with 0x48f64 in Hms. change (SR.ps_regs PtpA16.ps0) with (map (fun i => (i, nth i PtpA16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpA16.ps0) with PtpA16.cells0 in Hcells. unfold PtpA16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpA16.regs0 PtpA16.regs_out0 64 KS_tpA16 KS_tpA16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpA16.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtpA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpB := LibSegY_tpB.
Definition KS_tpB : list nat := Eval vm_compute in (BG.kept_list 64 PtpB.regs0 PtpB.regs_out0).
Lemma KS_tpB_ok : BG.kept_ok 64 PtpB.regs0 PtpB.regs_out0 KS_tpB = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 (V 33%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 8) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 44) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 8) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 44) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e17c M) (st fx' R' 0x8e740 M')
        /\ (forall x, In x KS_tpB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582288
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 581896
        /\ getr R' (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 40%nat)
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450923) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450922) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450921) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450920) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450915) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450914) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450913) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450912) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450907) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450906) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450905) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450904) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450899) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450898) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450897) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450896) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450891) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450890) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450889) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450888) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450903) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450902) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450900) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 581896
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) 97899
        /\ L5.u64_at RSEGS M' (V 40%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 40%nat)
        /\ L5.defined M' ((V 40%nat) + 24) 488
        /\ L5KA.zeros_at M' (((V 40%nat) / 8) + 2147450908) 4
        /\ L5KA.zeros_at M' (((V 40%nat) / 8) + 2147450916) 4
        /\ L5KA.zeros_at M' (((V 40%nat) / 8) + 2147450924) 20).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] G1 G2 G9 G10 G18 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpB.kn0).
  { unfold know_ok, PtpB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K18 K19; lia | clear - HV2l HV2r K0l K0r K18 K19; lia | clear - HV2l HV2r K0l K0r K18 K19; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19) | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | clear - HV40l HV40r K6l K6r K10 K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K14l K14r K16 K17 K19; lia | clear - HV41l HV41r K14l K14r K16 K17 K19; lia | clear - HV41l HV41r K14l K14r K16 K17 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpB.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 8) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 44) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PtpB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpB.ps0) with 0x8e740 in Hms. change (SR.ps_regs PtpB.ps0) with (map (fun i => (i, nth i PtpB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpB.ps0) with PtpB.cells0 in Hcells. unfold PtpB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpB.regs0 PtpB.regs_out0 64 KS_tpB KS_tpB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpB.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PtpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpCbig := LibSegY_tpCbig.
Definition KS_tpCbig : list nat := Eval vm_compute in (BG.kept_list 64 PtpCbig.regs0 PtpCbig.regs_out0).
Lemma KS_tpCbig_ok : BG.kept_ok 64 PtpCbig.regs0 PtpCbig.regs_out0 KS_tpCbig = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpCbig_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 5000 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e290 M) (st fx' R' 0x8e408 M')
        /\ (forall x, In x KS_tpCbig -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) / 8)
        /\ getr R' (reg 11) = Z_to_bv 64 624).
Proof.
  intros [HV2l HV2r] [HV34l HV34r] [HV40l HV40r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpCbig.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpCbig.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpCbig.kn0).
  { unfold know_ok, PtpCbig.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  destruct (PtpCbig.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpCbig.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpCbig.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpCbig.ps0) with 0x8e408 in Hms. change (SR.ps_regs PtpCbig.ps0) with (map (fun i => (i, nth i PtpCbig.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpCbig.ps0) with PtpCbig.cells0 in Hcells. unfold PtpCbig.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpCbig.regs0 PtpCbig.regs_out0 64 KS_tpCbig KS_tpCbig_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpCbig.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpCbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpCbig.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpCbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpC := LibSegY_tpC.
Definition KS_tpC : list nat := Eval vm_compute in (BG.kept_list 64 PtpC.regs0 PtpC.regs_out0).
Lemma KS_tpC_ok : BG.kept_ok 64 PtpC.regs0 PtpC.regs_out0 KS_tpC = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> 0 <= (V 34%nat) <= 4999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450892) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450892) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450892) <= i < (((V 40%nat) / 8) + 2147450892) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e290 M) (st fx' R' 0x8e8a8 M')
        /\ (forall x, In x KS_tpC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582340
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 11) = Z_to_bv 64 141664
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 0).
Proof.
  intros [HV2l HV2r] [HV34l HV34r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpC.kn0).
  { unfold know_ok, PtpC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  destruct (PtpC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpC.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 40%nat) / 8) + 2147450892) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450892) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpC.ps0) with 0x8e8a8 in Hms. change (SR.ps_regs PtpC.ps0) with (map (fun i => (i, nth i PtpC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpC.ps0) with PtpC.cells0 in Hcells. unfold PtpC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpC.regs0 PtpC.regs_out0 64 KS_tpC KS_tpC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpC.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtpC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpD := LibSegY_tpD.
Definition KS_tpD : list nat := Eval vm_compute in (BG.kept_list 64 PtpD.regs0 PtpD.regs_out0).
Lemma KS_tpD_ok : BG.kept_ok 64 PtpD.regs0 PtpD.regs_out0 KS_tpD = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450900) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450900) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450900) <= i < (((V 40%nat) / 8) + 2147450900) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e2c4 M) (st fx' R' 0x8e9ac M')
        /\ (forall x, In x KS_tpD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 160)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 40%nat) + 160)
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450903) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450902) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450900) 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpD.kn0).
  { unfold know_ok, PtpD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpD.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 40%nat) / 8) + 2147450900) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450900) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpD.ps0) with 0x8e9ac in Hms. change (SR.ps_regs PtpD.ps0) with (map (fun i => (i, nth i PtpD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpD.ps0) with PtpD.cells0 in Hcells. unfold PtpD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpD.regs0 PtpD.regs_out0 64 KS_tpD KS_tpD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpD.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpE := LibSegY_tpE.
Definition KS_tpE : list nat := Eval vm_compute in (BG.kept_list 64 PtpE.regs0 PtpE.regs_out0).
Lemma KS_tpE_ok : BG.kept_ok 64 PtpE.regs0 PtpE.regs_out0 KS_tpE = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e2e4 M) (st fx' R' 0x920c4 M')
        /\ (forall x, In x KS_tpE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582388
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 224)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 40%nat) + 224)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G23 G27 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpE.kn0).
  { unfold know_ok, PtpE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtpE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpE.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpE.ps0) with 0x920c4 in Hms. change (SR.ps_regs PtpE.ps0) with (map (fun i => (i, nth i PtpE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpE.ps0) with PtpE.cells0 in Hcells. unfold PtpE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpE.regs0 PtpE.regs_out0 64 KS_tpE KS_tpE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PtpE.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpF := LibSegY_tpF.
Definition KS_tpF : list nat := Eval vm_compute in (BG.kept_list 64 PtpF.regs0 PtpF.regs_out0).
Lemma KS_tpF_ok : BG.kept_ok 64 PtpF.regs0 PtpF.regs_out0 KS_tpF = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e2f4 M) (st fx' R' 0x8eb0c M')
        /\ (forall x, In x KS_tpF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582404
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 224)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 160)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G23 G26 G27 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpF.kn0).
  { unfold know_ok, PtpF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtpF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpF.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpF.ps0) with 0x8eb0c in Hms. change (SR.ps_regs PtpF.ps0) with (map (fun i => (i, nth i PtpF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpF.ps0) with PtpF.cells0 in Hcells. unfold PtpF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpF.regs0 PtpF.regs_out0 64 KS_tpF KS_tpF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpHi := LibSegY_tpHi.
Definition KS_tpHi : list nat := Eval vm_compute in (BG.kept_list 64 PtpHi.regs0 PtpHi.regs_out0).
Lemma KS_tpHi_ok : BG.kept_ok 64 PtpHi.regs0 PtpHi.regs_out0 KS_tpHi = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpHi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 224) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e304 M) (st fx' R' 0x8e328 M')
        /\ (forall x, In x KS_tpHi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 40%nat) + 288)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G21 G23 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpHi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpHi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpHi.kn0).
  { unfold know_ok, PtpHi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpHi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpHi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpHi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpHi.ps0) with 0x8e328 in Hms. change (SR.ps_regs PtpHi.ps0) with (map (fun i => (i, nth i PtpHi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpHi.ps0) with PtpHi.cells0 in Hcells. unfold PtpHi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpHi.regs0 PtpHi.regs_out0 64 KS_tpHi KS_tpHi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpHi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpHi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpHi.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PtpHi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpHd := LibSegY_tpHd.
Definition KS_tpHd : list nat := Eval vm_compute in (BG.kept_list 64 PtpHd.regs0 PtpHd.regs_out0).
Lemma KS_tpHd_ok : BG.kept_ok 64 PtpHd.regs0 PtpHd.regs_out0 KS_tpHd = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpHd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 224) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 248) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 40%nat) + 240) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e304 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpHd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582440
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 40%nat) + 288)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G21 G23 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpHd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpHd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpHd.kn0).
  { unfold know_ok, PtpHd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (PtpHd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpHd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpHd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpHd.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpHd.ps0) with (map (fun i => (i, nth i PtpHd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpHd.ps0) with PtpHd.cells0 in Hcells. unfold PtpHd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpHd.regs0 PtpHd.regs_out0 64 KS_tpHd KS_tpHd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpHd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpHd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpHd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpHd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpHd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpHd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpHd.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PtpHd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpH2 := LibSegY_tpH2.
Definition KS_tpH2 : list nat := Eval vm_compute in (BG.kept_list 64 PtpH2.regs0 PtpH2.regs_out0).
Lemma KS_tpH2_ok : BG.kept_ok 64 PtpH2.regs0 PtpH2.regs_out0 KS_tpH2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpH2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e328 M) (st fx' R' 0x920c4 M')
        /\ (forall x, In x KS_tpH2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582452
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 288)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 160)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpH2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpH2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpH2.kn0).
  { unfold know_ok, PtpH2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtpH2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpH2.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpH2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpH2.ps0) with 0x920c4 in Hms. change (SR.ps_regs PtpH2.ps0) with (map (fun i => (i, nth i PtpH2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpH2.ps0) with PtpH2.cells0 in Hcells. unfold PtpH2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpH2.regs0 PtpH2.regs_out0 64 KS_tpH2 KS_tpH2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpH2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpH2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpH2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpI := LibSegY_tpI.
Definition KS_tpI : list nat := Eval vm_compute in (BG.kept_list 64 PtpI.regs0 PtpI.regs_out0).
Lemma KS_tpI_ok : BG.kept_ok 64 PtpI.regs0 PtpI.regs_out0 KS_tpI = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e334 M) (st fx' R' 0x8eb0c M')
        /\ (forall x, In x KS_tpI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582468
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 168)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 288)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 96)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpI.kn0).
  { unfold know_ok, PtpI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtpI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpI.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpI.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpI.ps0) with 0x8eb0c in Hms. change (SR.ps_regs PtpI.ps0) with (map (fun i => (i, nth i PtpI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpI.ps0) with PtpI.cells0 in Hcells. unfold PtpI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpI.regs0 PtpI.regs_out0 64 KS_tpI KS_tpI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ATP1.
