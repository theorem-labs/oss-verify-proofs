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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_rzA LibSegY_rzB LibSegY_rzCge LibSegY_rzCi0 LibSegY_rzCi1 LibSegY_rzCd LibSegY_rzE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ARZP.
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
Module PrzA := LibSegY_rzA.
Definition KS_rzA : list nat := Eval vm_compute in (BG.kept_list 56 PrzA.regs0 PrzA.regs_out0).
Lemma KS_rzA_ok : BG.kept_ok 56 PrzA.regs0 PrzA.regs_out0 KS_rzA = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fca4 M) (st fx' R' 0x48c38 M')
        /\ (forall x, In x KS_rzA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 589076
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 911160
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 2147450880
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
  assert (HR: regs_ok E PrzA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzA.kn0).
  { unfold know_ok, PrzA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PrzA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzA.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PrzA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzA.ps0) with 0x48c38 in Hms. change (SR.ps_regs PrzA.ps0) with (map (fun i => (i, nth i PrzA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzA.ps0) with PrzA.cells0 in Hcells. unfold PrzA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzA.regs0 PrzA.regs_out0 56 KS_rzA KS_rzA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PrzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
Module PrzB := LibSegY_rzB.
Definition KS_rzB : list nat := Eval vm_compute in (BG.kept_list 56 PrzB.regs0 PrzB.regs_out0).
Lemma KS_rzB_ok : BG.kept_ok 56 PrzB.regs0 PrzB.regs_out0 KS_rzB = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 47%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18))) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25))) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26))) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 4096 <= (V 40%nat) <= 140737488355200 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 ->
  (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 35%nat) -> 0 <= (V 35%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= i < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fd14 M) (st fx' R' 0x900dc M')
        /\ (forall x, In x KS_rzB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 589268
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 588964
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
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
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 588964
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) 135661
        /\ L5.u64_at RSEGS M' (V 40%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.defined M' ((V 40%nat) + 24) 104).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] G1 G2 G8 G9 G10 G19 G20 G24 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 K39 K40 K41 [K42l K42r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PrzB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzB.kn0).
  { unfold know_ok, PrzB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear - HV35l HV35r K42l K42r) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_nil. }
  destruct (PrzB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzB.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PrzB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzB.ps0) with 0x900dc in Hms. change (SR.ps_regs PrzB.ps0) with (map (fun i => (i, nth i PrzB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzB.ps0) with PrzB.cells0 in Hcells. unfold PrzB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzB.regs0 PrzB.regs_out0 56 KS_rzB KS_rzB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PrzB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzCge := LibSegY_rzCge.
Definition KS_rzCge : list nat := Eval vm_compute in (BG.kept_list 56 PrzCge.regs0 PrzCge.regs_out0).
Lemma KS_rzCge_ok : BG.kept_ok 56 PrzCge.regs0 PrzCge.regs_out0 KS_rzCge = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzCge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 47%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 35%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 4096 <= (V 40%nat) <= 140737488355200 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 ->
  (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) -> 0 <= (V 34%nat) <= 8388608 -> 0 <= (V 35%nat) <= 134217728 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> (V 34%nat) <= (V 35%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= i < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fdd4 M) (st fx' R' 0x8ff64 M')
        /\ (forall x, In x KS_rzCge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 54%nat)
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
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 34%nat)
        /\ L5.defined M' ((V 40%nat) + 8) 120).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 K39 K40 [K41l K41r] [K42l K42r] K43 [K44l K44r] K45.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PrzCge.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzCge.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzCge.kn0).
  { unfold know_ok, PrzCge.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K45) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K42l K42r K45) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear - HV36l HV36r K44l K44r) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | byte_tac ltac:(clear - HV36l HV36r K44l K44r) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K45; clear; intro; destruct (Z.ltb_spec0 (V 35%nat) (V 34%nat)); lia]. }
    apply Forall_nil. }
  destruct (PrzCge.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzCge.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply Hfr. unfold PrzCge.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40 Hn5; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzCge.ps0) with 0x8ff64 in Hms. change (SR.ps_regs PrzCge.ps0) with (map (fun i => (i, nth i PrzCge.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzCge.ps0) with PrzCge.cells0 in Hcells. unfold PrzCge.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzCge.regs0 PrzCge.regs_out0 56 KS_rzCge KS_rzCge_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCge.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PrzCge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K41l K41r K45) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzCi0 := LibSegY_rzCi0.
Definition KS_rzCi0 : list nat := Eval vm_compute in (BG.kept_list 56 PrzCi0.regs0 PrzCi0.regs_out0).
Lemma KS_rzCi0_ok : BG.kept_ok 56 PrzCi0.regs0 PrzCi0.regs_out0 KS_rzCi0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzCi0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 47%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 4096 <= (V 40%nat) <= 140737488355200 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 ->
  (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) -> 0 <= (V 34%nat) <= 8388608 -> 0 <= (V 35%nat) <= 134217728 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> 1 <= (V 34%nat) <= 2 -> 0 < (V 34%nat) -> (V 34%nat) <= 2 ->
  Z.testbit (V 36%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= i < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fdd4 M) (st fx' R' 0x8ff64 M')
        /\ (forall x, In x KS_rzCi0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 33%nat)) - 17)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 54%nat)
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
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 34%nat)
        /\ L5.defined M' ((V 40%nat) + 8) 120).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 K39 K40 [K41l K41r] [K42l K42r] K43 [K44l K44r] [K45l K45r] K46 K47 K48.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PrzCi0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzCi0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzCi0.kn0).
  { unfold know_ok, PrzCi0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K45l K45r K46 K47) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K48) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | byte_tac ltac:(clear - HV36l HV36r K44l K44r K48) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K48) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K45l K45r K46 K47) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K46; clear; intro; destruct (Z.ltb_spec0 0 (V 34%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K47; clear; intro; destruct (Z.ltb_spec0 2 (V 34%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K48) | clear; lia | rewrite (L5K.land1_bit0_false (V 36%nat) ltac:(clear - HV36l HV36r K44l K44r K48; lia) K48); clear; lia]. }
    apply Forall_nil. }
  destruct (PrzCi0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzCi0.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 24) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply Hfr. unfold PrzCi0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40 Hn5; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzCi0.ps0) with 0x8ff64 in Hms. change (SR.ps_regs PrzCi0.ps0) with (map (fun i => (i, nth i PrzCi0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzCi0.ps0) with PrzCi0.cells0 in Hcells. unfold PrzCi0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzCi0.regs0 PrzCi0.regs_out0 56 KS_rzCi0 KS_rzCi0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PrzCi0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K41l K41r K45l K45r K46 K47) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzCi1 := LibSegY_rzCi1.
Definition KS_rzCi1 : list nat := Eval vm_compute in (BG.kept_list 56 PrzCi1.regs0 PrzCi1.regs_out0).
Lemma KS_rzCi1_ok : BG.kept_ok 56 PrzCi1.regs0 PrzCi1.regs_out0 KS_rzCi1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzCi1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 47%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 4096 <= (V 40%nat) <= 140737488355200 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 ->
  (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) -> 0 <= (V 34%nat) <= 8388608 -> 0 <= (V 35%nat) <= 134217728 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> Z.testbit (V 36%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= i < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fdd4 M) (st fx' R' 0x8ff64 M')
        /\ (forall x, In x KS_rzCi1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 33%nat)) - 17)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 54%nat)
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
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) 2
        /\ L5.defined M' ((V 40%nat) + 8) 120).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 K39 K40 [K41l K41r] [K42l K42r] K43 [K44l K44r] K45.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PrzCi1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzCi1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzCi1.kn0).
  { unfold know_ok, PrzCi1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K45) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | byte_tac ltac:(clear - HV36l HV36r K44l K44r K45) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K45) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K45) | clear; lia | rewrite (L5K.land1_bit0_false (V 36%nat) ltac:(clear - HV36l HV36r K44l K44r K45; lia) K45); clear; lia]. }
    apply Forall_nil. }
  destruct (PrzCi1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzCi1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PrzCi1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40 Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzCi1.ps0) with 0x8ff64 in Hms. change (SR.ps_regs PrzCi1.ps0) with (map (fun i => (i, nth i PrzCi1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzCi1.ps0) with PrzCi1.cells0 in Hcells. unfold PrzCi1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzCi1.regs0 PrzCi1.regs_out0 56 KS_rzCi1 KS_rzCi1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCi1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PrzCi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzCd := LibSegY_rzCd.
Definition KS_rzCd : list nat := Eval vm_compute in (BG.kept_list 56 PrzCd.regs0 PrzCd.regs_out0).
Lemma KS_rzCd_ok : BG.kept_ok 56 PrzCd.regs0 PrzCd.regs_out0 KS_rzCd = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzCd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 47%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 35%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 4096 <= (V 40%nat) <= 140737488355200 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 ->
  (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) -> 0 <= (V 34%nat) <= 8388608 -> 0 <= (V 35%nat) <= 134217728 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> (V 35%nat) < (V 34%nat) -> Z.testbit (V 36%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 37%nat) ->
  4096 <= (V 37%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fdd4 M) (st fx' R' 0x5e7f0 M')
        /\ (forall x, In x KS_rzCd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 589468
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * (V 35%nat)) + (V 37%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((8 * (V 34%nat)) + ((-8) * (V 35%nat)))
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 K39 K40 [K41l K41r] [K42l K42r] K43 [K44l K44r] K45 K46 K47 [K48l K48r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PrzCd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzCd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzCd.kn0).
  { unfold know_ok, PrzCd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K45) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K42l K42r K45) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K46) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | byte_tac ltac:(clear - HV36l HV36r K44l K44r K46) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K46) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [L5K.evalB ZA; reflexivity | generalize K45; clear; intro; destruct (Z.ltb_spec0 (V 35%nat) (V 34%nat)); lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K44l K44r K46) | clear; lia | rewrite (L5K.land1_bit0_true (V 36%nat) ltac:(clear - HV36l HV36r K44l K44r K46; lia) K46); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear - HV37l HV37r K48l K48r) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K48l K48r) | exact (conj K48l K48r)]. }
    apply Forall_nil. }
  destruct (PrzCd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzCd.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PrzCd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzCd.ps0) with 0x5e7f0 in Hms. change (SR.ps_regs PrzCd.ps0) with (map (fun i => (i, nth i PrzCd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzCd.ps0) with PrzCd.cells0 in Hcells. unfold PrzCd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzCd.regs0 PrzCd.regs_out0 56 KS_rzCd KS_rzCd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzCd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzCd.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzCd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K41l K41r K45) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV53l HV53r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear - HV54l HV54r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzE := LibSegY_rzE.
Definition KS_rzE : list nat := Eval vm_compute in (BG.kept_list 56 PrzE.regs0 PrzE.regs_out0).
Lemma KS_rzE_ok : BG.kept_ok 56 PrzE.regs0 PrzE.regs_out0 KS_rzE = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 47%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 40%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 (V 35%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> 4096 <= (V 40%nat) <= 140737488355200 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 ->
  (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= i < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8fe9c M) (st fx' R' 0x8ff64 M')
        /\ (forall x, In x KS_rzE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 54%nat)
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
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 K39 K40.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PrzE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzE.kn0).
  { unfold know_ok, PrzE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | clear - HV2l HV2r K0l K0r K30 K31 K40; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | clear - HV41l HV41r K26l K26r K28 K29 K31 K33; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K32 K33 K34 K35l K35r K37 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PrzE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PrzE.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ (((V 40%nat) + 32) <= bv_unsigned a < ((V 40%nat) + 32) + 88) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PrzE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K30 K31 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31 K40 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 K33 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzE.ps0) with 0x8ff64 in Hms. change (SR.ps_regs PrzE.ps0) with (map (fun i => (i, nth i PrzE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzE.ps0) with PrzE.cells0 in Hcells. unfold PrzE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzE.regs0 PrzE.regs_out0 56 KS_rzE KS_rzE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PrzE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31 K33) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30 K32 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5ARZP.
