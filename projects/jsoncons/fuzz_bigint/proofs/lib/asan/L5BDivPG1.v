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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_v5G1 LibSegY_v5G2 LibSegY_v5G3 LibSegY_v5G4i LibSegY_v5G4d LibSegY_v5G5i0 LibSegY_v5G5in LibSegY_v5G5d0 LibSegY_v5G5dn LibSegY_v5G6 LibSegY_v5G7i LibSegY_v5G7d LibSegY_v5G7b LibSegY_v5G8i LibSegY_v5G8d LibSegY_v5G8bi LibSegY_v5G8bd.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ADIVPG1.
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
Module Pv5G1 := LibSegY_v5G1.
Definition KS_v5G1 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G1.regs0 Pv5G1.regs_out0).
Lemma KS_v5G1_ok : BG.kept_ok 96 Pv5G1.regs0 Pv5G1.regs_out0 KS_v5G1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 360) <= bv_unsigned a < ((V 2%nat) - 360) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 360) <= i < ((V 2%nat) - 360) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x930a8 M) (st fx' R' 0x944c0 M')
        /\ (forall x, In x KS_v5G1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602300
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 360) (V 40%nat)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV58l HV58r] G1 G2 G8 G9 G23 G25 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E Pv5G1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G1.kn0).
  { unfold know_ok, Pv5G1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  destruct (Pv5G1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G1.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 360) <= bv_unsigned a < ((V 2%nat) - 360) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G1.ps0) with 0x944c0 in Hms. change (SR.ps_regs Pv5G1.ps0) with (map (fun i => (i, nth i Pv5G1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G1.ps0) with Pv5G1.cells0 in Hcells. unfold Pv5G1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G1.regs0 Pv5G1.regs_out0 96 KS_v5G1 KS_v5G1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G2 := LibSegY_v5G2.
Definition KS_v5G2 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G2.regs0 Pv5G2.regs_out0).
Lemma KS_v5G2_ok : BG.kept_ok 96 Pv5G2.regs0 Pv5G2.regs_out0 KS_v5G2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 304) ((V 40%nat) + 32) -> 4096 <= (V 40%nat) <= 140737488354816 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x930bc M) (st fx' R' 0x944c0 M')
        /\ (forall x, In x KS_v5G2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602320
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 216)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) + 32)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV58l HV58r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E Pv5G2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G2.kn0).
  { unfold know_ok, Pv5G2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r K7l K7r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (Pv5G2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G2.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G2.ps0) with 0x944c0 in Hms. change (SR.ps_regs Pv5G2.ps0) with (map (fun i => (i, nth i Pv5G2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G2.ps0) with Pv5G2.cells0 in Hcells. unfold Pv5G2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G2.regs0 Pv5G2.regs_out0 96 KS_v5G2 KS_v5G2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5G2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G3 := LibSegY_v5G3.
Definition KS_v5G3 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G3.regs0 Pv5G3.regs_out0).
Lemma KS_v5G3_ok : BG.kept_ok 96 Pv5G3.regs0 Pv5G3.regs_out0 KS_v5G3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 96) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 0 <= (V 33%nat) <= 18446744073709551615 -> 4096 <= (V 40%nat) <= 140737488354816 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 220) <= bv_unsigned a < ((V 2%nat) - 220) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 220) <= i < ((V 2%nat) - 220) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x930d0 M) (st fx' R' 0x93d94 M')
        /\ (forall x, In x KS_v5G3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602344
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 220)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 220) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV40l HV40r] [HV58l HV58r] G1 G2 G8 G9 G19 G21 G23 G25 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E Pv5G3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G3.kn0).
  { unfold know_ok, Pv5G3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (Pv5G3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G3.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 220) <= bv_unsigned a < ((V 2%nat) - 220) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G3.ps0) with 0x93d94 in Hms. change (SR.ps_regs Pv5G3.ps0) with (map (fun i => (i, nth i Pv5G3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G3.ps0) with Pv5G3.cells0 in Hcells. unfold Pv5G3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G3.regs0 Pv5G3.regs_out0 96 KS_v5G3 KS_v5G3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G4i := LibSegY_v5G4i.
Definition KS_v5G4i : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G4i.regs0 Pv5G4i.regs_out0).
Lemma KS_v5G4i_ok : BG.kept_ok 96 Pv5G4i.regs0 Pv5G4i.regs_out0 KS_v5G4i = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G4i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 10) = Z_to_bv 64 (V 63%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 96) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 384) + 384 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 384)) -> (((V 2%nat) - 384) + 384 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 384)) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) ->
  0 <= (V 63%nat) <= 18446744073709551615 -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450884) 4 -> L5.u8_at RSEGS M ((V 40%nat) + 32) (V 55%nat) ->
  0 <= (V 55%nat) <= 255 -> Z.testbit (V 55%nat) 0 = false -> L5.u64_at RSEGS M ((V 40%nat) + 40) (V 64%nat) -> 0 <= (V 64%nat) <= 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 40%nat) + 104) (V 66%nat) -> 0 <= (V 66%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 16) -> ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 16) -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x930e8 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_v5G4i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602428
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 64%nat)) + (V 66%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 63%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 40%nat) + 48)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV55l HV55r] [HV58l HV58r] [HV63l HV63r] [HV64l HV64r] [HV66l HV66r] G1 G2 G8 G9 G10 G19 G23 G25 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] [K21l K21r] K22 K23 [K24l K24r] K25 K26 [K27l K27r] K28 [K29l K29r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 55%nat => (V 55%nat) | 58%nat => (V 58%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 66%nat => (V 66%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 67%nat. }
  assert (HR: regs_ok E Pv5G4i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G4i.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G4i.kn0).
  { unfold know_ok, Pv5G4i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV41l HV41r K13l K13r K15 K16 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV41l HV41r K13l K13r K15 K16 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV35l HV35r K21l K21r) | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV55l HV55r K24l K24r K25) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV55l HV55r K24l K24r K25) | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K24l K24r K25) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV55l HV55r K24l K24r K25) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 55%nat) ltac:(clear - HV55l HV55r K24l K24r K25; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K25); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV66l HV66r K29l K29r) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_nil. }
  destruct (Pv5G4i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G4i.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 16) -> ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5G4i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G4i.ps0) with 0x8fca4 in Hms. change (SR.ps_regs Pv5G4i.ps0) with (map (fun i => (i, nth i Pv5G4i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G4i.ps0) with Pv5G4i.cells0 in Hcells. unfold Pv5G4i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G4i.regs0 Pv5G4i.regs_out0 96 KS_v5G4i KS_v5G4i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G4i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4i.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5G4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4i.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5G4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K27l K27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K27l K27r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G4d := LibSegY_v5G4d.
Definition KS_v5G4d : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G4d.regs0 Pv5G4d.regs_out0).
Lemma KS_v5G4d_ok : BG.kept_ok 96 Pv5G4d.regs0 Pv5G4d.regs_out0 KS_v5G4d = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G4d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 10) = Z_to_bv 64 (V 63%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 96) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 384) + 384 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 384)) -> (((V 2%nat) - 384) + 384 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 384)) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) ->
  0 <= (V 63%nat) <= 18446744073709551615 -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450884) 4 -> L5.u8_at RSEGS M ((V 40%nat) + 32) (V 55%nat) ->
  0 <= (V 55%nat) <= 255 -> Z.testbit (V 55%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 56) (V 65%nat) ->
  4096 <= (V 65%nat) <= 140737488355328 -> aligned (V 65%nat) 8 -> 0 <= (V 64%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 40%nat) + 104) (V 66%nat) ->
  0 <= (V 66%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 16) -> ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 16) -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x930e8 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_v5G4d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602428
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 64%nat)) + (V 66%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 63%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 65%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV55l HV55r] [HV58l HV58r] [HV63l HV63r] [HV64l HV64r] [HV65l HV65r] [HV66l HV66r] G1 G2 G8 G9 G10 G19 G23 G25 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] [K21l K21r] K22 K23 [K24l K24r] K25 K26 K27 [K28l K28r] K29 [K30l K30r] K31 [K32l K32r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 55%nat => (V 55%nat) | 58%nat => (V 58%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 67%nat. }
  assert (HR: regs_ok E Pv5G4d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G4d.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G4d.kn0).
  { unfold know_ok, Pv5G4d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV41l HV41r K13l K13r K15 K16 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV41l HV41r K13l K13r K15 K16 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV35l HV35r K21l K21r) | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K17 K18; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV55l HV55r K24l K24r K25) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV55l HV55r K24l K24r K25) | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K24l K24r K25) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV55l HV55r K24l K24r K25) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 55%nat) ltac:(clear - HV55l HV55r K24l K24r K25; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K25); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV64l HV64r K30l K30r) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV65l HV65r K28l K28r) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV65l HV65r K28l K28r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K29]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV66l HV66r K32l K32r) | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV40l HV40r K6l K6r K10 K16 K17; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_nil. }
  destruct (Pv5G4d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G4d.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 16) -> ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5G4d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G4d.ps0) with 0x8fca4 in Hms. change (SR.ps_regs Pv5G4d.ps0) with (map (fun i => (i, nth i Pv5G4d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G4d.ps0) with Pv5G4d.cells0 in Hcells. unfold Pv5G4d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G4d.regs0 Pv5G4d.regs_out0 96 KS_v5G4d KS_v5G4d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G4d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4d.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4d.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5G4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G4d.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5G4d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K30l K30r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear - HV64l HV64r K30l K30r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk' ZA Hag ltac:(clear - HV65l HV65r K28l K28r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G5i0 := LibSegY_v5G5i0.
Definition KS_v5G5i0 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G5i0.regs0 Pv5G5i0.regs_out0).
Lemma KS_v5G5i0_ok : BG.kept_ok 96 Pv5G5i0.regs0 Pv5G5i0.regs_out0 KS_v5G5i0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G5i0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 35%nat) + 8) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 352) ((((V 35%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> L5.u8_at RSEGS M (V 35%nat) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 67%nat) -> 0 <= (V 67%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9313c M) (st fx' R' 0x931c4 M')
        /\ (forall x, In x KS_v5G5i0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV67l HV67r] G1 G2 G8 G9 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 67%nat => (V 67%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 68%nat. }
  assert (HR: regs_ok E Pv5G5i0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G5i0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G5i0.kn0).
  { unfold know_ok, Pv5G5i0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K21); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r K23l K23r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  destruct (Pv5G5i0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G5i0.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G5i0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G5i0.ps0) with 0x931c4 in Hms. change (SR.ps_regs Pv5G5i0.ps0) with (map (fun i => (i, nth i Pv5G5i0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G5i0.ps0) with Pv5G5i0.cells0 in Hcells. unfold Pv5G5i0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G5i0.regs0 Pv5G5i0.regs_out0 96 KS_v5G5i0 KS_v5G5i0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G5i0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G5i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5i0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G5i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5i0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G5i0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G5in := LibSegY_v5G5in.
Definition KS_v5G5in : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G5in.regs0 Pv5G5in.regs_out0).
Lemma KS_v5G5in_ok : BG.kept_ok 96 Pv5G5in.regs0 Pv5G5in.regs_out0 KS_v5G5in = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G5in_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 35%nat) + 8) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 352) ((((V 35%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> L5.u8_at RSEGS M (V 35%nat) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 67%nat) -> 1 <= (V 67%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9313c M) (st fx' R' 0x9319c M')
        /\ (forall x, In x KS_v5G5in -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 67%nat) - 1)
        /\ getr R' (reg 21) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV67l HV67r] G1 G2 G8 G9 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 67%nat => (V 67%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 68%nat. }
  assert (HR: regs_ok E Pv5G5in.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G5in.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G5in.kn0).
  { unfold know_ok, Pv5G5in.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K21); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r K23l K23r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  destruct (Pv5G5in.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G5in.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G5in.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G5in.ps0) with 0x9319c in Hms. change (SR.ps_regs Pv5G5in.ps0) with (map (fun i => (i, nth i Pv5G5in.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G5in.ps0) with Pv5G5in.cells0 in Hcells. unfold Pv5G5in.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G5in.regs0 Pv5G5in.regs_out0 96 KS_v5G5in KS_v5G5in_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G5in.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G5in.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5in.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G5in.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5in.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G5in.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5in.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5G5in.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV67l HV67r K23l K23r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G5d0 := LibSegY_v5G5d0.
Definition KS_v5G5d0 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G5d0.regs0 Pv5G5d0.regs_out0).
Lemma KS_v5G5d0_ok : BG.kept_ok 96 Pv5G5d0.regs0 Pv5G5d0.regs_out0 KS_v5G5d0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G5d0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 35%nat) + 8) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 352) ((((V 35%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> L5.u8_at RSEGS M (V 35%nat) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 67%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 68%nat) ->
  4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 -> 0 <= (V 67%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9313c M) (st fx' R' 0x931c4 M')
        /\ (forall x, In x KS_v5G5d0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 68%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV67l HV67r] [HV68l HV68r] G1 G2 G8 G9 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 K23 [K24l K24r] K25 [K26l K26r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pv5G5d0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G5d0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G5d0.kn0).
  { unfold know_ok, Pv5G5d0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K21); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r K26l K26r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r K24l K24r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K24l K24r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  destruct (Pv5G5d0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G5d0.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G5d0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G5d0.ps0) with 0x931c4 in Hms. change (SR.ps_regs Pv5G5d0.ps0) with (map (fun i => (i, nth i Pv5G5d0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G5d0.ps0) with Pv5G5d0.cells0 in Hcells. unfold Pv5G5d0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G5d0.regs0 Pv5G5d0.regs_out0 96 KS_v5G5d0 KS_v5G5d0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G5d0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G5d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5d0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G5d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5d0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G5d0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV68l HV68r K24l K24r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G5dn := LibSegY_v5G5dn.
Definition KS_v5G5dn : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G5dn.regs0 Pv5G5dn.regs_out0).
Lemma KS_v5G5dn_ok : BG.kept_ok 96 Pv5G5dn.regs0 Pv5G5dn.regs_out0 KS_v5G5dn = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G5dn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 35%nat) + 8) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 352) ((((V 35%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> L5.u8_at RSEGS M (V 35%nat) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 67%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 24) (V 68%nat) ->
  4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 -> 1 <= (V 67%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9313c M) (st fx' R' 0x9319c M')
        /\ (forall x, In x KS_v5G5dn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 67%nat) - 1)
        /\ getr R' (reg 21) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 68%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV67l HV67r] [HV68l HV68r] G1 G2 G8 G9 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 K23 [K24l K24r] K25 [K26l K26r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pv5G5dn.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G5dn.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G5dn.kn0).
  { unfold know_ok, Pv5G5dn.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K21); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r K26l K26r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r K24l K24r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K24l K24r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  destruct (Pv5G5dn.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G5dn.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G5dn.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G5dn.ps0) with 0x9319c in Hms. change (SR.ps_regs Pv5G5dn.ps0) with (map (fun i => (i, nth i Pv5G5dn.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G5dn.ps0) with Pv5G5dn.cells0 in Hcells. unfold Pv5G5dn.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G5dn.regs0 Pv5G5dn.regs_out0 96 KS_v5G5dn KS_v5G5dn_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G5dn.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G5dn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5dn.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G5dn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5dn.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G5dn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5dn.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5G5dn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV67l HV67r K26l K26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV68l HV68r K24l K24r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G6 := LibSegY_v5G6.
Definition KS_v5G6 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G6.regs0 Pv5G6.regs_out0).
Lemma KS_v5G6_ok : BG.kept_ok 96 Pv5G6.regs0 Pv5G6.regs_out0 KS_v5G6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 96) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 36%nat) -> 0 <= (V 36%nat) <= 18446744073709551615 ->
  4096 <= (V 40%nat) <= 140737488354816 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x931c4 M) (st fx' R' 0x8fb14 M')
        /\ (forall x, In x KS_v5G6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602580
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV40l HV40r] [HV58l HV58r] G1 G2 G8 G9 G23 G25 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] [K8l K8r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E Pv5G6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G6.kn0).
  { unfold know_ok, Pv5G6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  destruct (Pv5G6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G6.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G6.ps0) with 0x8fb14 in Hms. change (SR.ps_regs Pv5G6.ps0) with (map (fun i => (i, nth i Pv5G6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G6.ps0) with Pv5G6.cells0 in Hcells. unfold Pv5G6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G6.regs0 Pv5G6.regs_out0 96 KS_v5G6 KS_v5G6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5G6.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5G6.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G7i := LibSegY_v5G7i.
Definition KS_v5G7i : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G7i.regs0 Pv5G7i.regs_out0).
Lemma KS_v5G7i_ok : BG.kept_ok 96 Pv5G7i.regs0 Pv5G7i.regs_out0 KS_v5G7i = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma v5G7i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 20) = Z_to_bv 64 ((V 73%nat) + 1) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 63%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 400) + 400 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 400)) -> ((V 36%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 36%nat)) ->
  ((V 36%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 400) \/ ((V 2%nat) - 400) + 400 <= (((V 36%nat) / 8) + 2147450880)) ->
  4096 <= ((V 36%nat) + 16) <= 140737488355328 -> aligned ((V 36%nat) + 16) 8 -> 4104 <= (((V 36%nat) + (8 * (V 71%nat))) + 16) <= 140737479966720 -> (2147446784 + 17592186048512 <= ((V 36%nat) + 16) \/ ((V 36%nat) + 16) + (8 * (V 71%nat)) <= 2147446784) ->
  1 <= (V 71%nat) <= 134217728 -> L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) (V 71%nat) -> (((V 36%nat) + 16) + (8 * (V 71%nat)) <= ((((V 36%nat) + 16) / 8) + 2147450880) \/ ((((V 36%nat) + 16) / 8) + 2147450880) + (V 71%nat) <= ((V 36%nat) + 16)) -> (((V 2%nat) - 400) + 400 <= ((V 36%nat) + 16) \/ ((V 36%nat) + 16) + (8 * (V 71%nat)) <= ((V 2%nat) - 400)) ->
  (((V 2%nat) - 400) + 400 <= ((((V 36%nat) + 16) / 8) + 2147450880) \/ ((((V 36%nat) + 16) / 8) + 2147450880) + (V 71%nat) <= ((V 2%nat) - 400)) -> 4096 <= (V 65%nat) <= 140737488355328 -> aligned (V 65%nat) 8 -> 4104 <= ((8 * (V 64%nat)) + (V 65%nat)) <= 140737479966720 ->
  (2147446784 + 17592186048512 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= 2147446784) -> 1 <= (V 64%nat) <= 134217728 -> L5KA.zeros_at M (((V 65%nat) / 8) + 2147450880) (V 64%nat) -> ((V 65%nat) + (8 * (V 64%nat)) <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= (V 65%nat)) ->
  (((V 2%nat) - 400) + 400 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= ((V 2%nat) - 400)) -> L5.u8_at RSEGS M (V 36%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = false -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 72%nat) -> 0 <= (V 72%nat) <= 18446744073709551615 -> 0 <= (V 63%nat) <= 18446744073709551615 ->
  0 <= (V 73%nat) <= 134217727 -> 0 <= (V 74%nat) <= 134217727 -> 1 <= ((V 71%nat) - (V 73%nat)) <= 134217728 -> 1 <= ((V 64%nat) - (V 74%nat)) <= 134217728 ->
  L5.u64_at RSEGS M ((V 2%nat) - 272) ((V 74%nat) + 1) -> L5KA.zeros_at M ((((V 2%nat) - 240) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 65%nat) -> L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 73%nat))) + 16) (V 76%nat) -> 0 <= (V 76%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 65%nat) + (8 * (V 74%nat))) (V 75%nat) -> 0 <= (V 75%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 376) <= bv_unsigned a < ((V 2%nat) - 376) + 16) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 376) <= i < ((V 2%nat) - 376) + 16) -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 16) -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x931d4 M) (st fx' R' 0x93284 M')
        /\ (forall x, In x KS_v5G7i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602736
        /\ getr R' (reg 10) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 36%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 74%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 602736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 36%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) (V 63%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) (((V 36%nat) / 8) + 2147450880)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV63l HV63r] [HV64l HV64r] [HV65l HV65r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] [HV75l HV75r] [HV76l HV76r] G1 G2 G8 G9 G20 G22 G23 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 [K16l K16r] K17 [K18l K18r] K19 [K20l K20r] K21 K22 K23 K24 [K25l K25r] K26 [K27l K27r] K28 [K29l K29r] K30 K31 K32 K33 K34 [K35l K35r] K36 K37 [K38l K38r] [K39l K39r] [K40l K40r] [K41l K41r] [K42l K42r] [K43l K43r] K44 K45 K46 K47 K48 [K49l K49r] K50 [K51l K51r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E Pv5G7i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G7i.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G7i.kn0).
  { unfold know_ok, Pv5G7i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV71l HV71r K20l K20r K42l K42r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | generalize K19; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV71l HV71r K20l K20r K42l K42r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV71l HV71r K20l K20r K42l K42r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV71l HV71r K20l K20r K42l K42r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | generalize K22; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | generalize K23; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r) | generalize K24; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r HV65l HV65r K25l K25r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | generalize K28; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r HV65l HV65r K25l K25r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r HV65l HV65r K25l K25r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r HV65l HV65r K25l K25r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | generalize K31; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | generalize K32; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r) | generalize K33; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV60l HV60r K35l K35r K36) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K35l K35r K36) | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K35l K35r K36) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K35l K35r K36) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K35l K35r K36; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K36); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | evalEk ZA ltac:(clear - HV72l HV72r K38l K38r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K38l K38r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K39l K39r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K40l K40r K42l K42r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K41l K41r K43l K43r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K42l K42r HV73l HV73r K40l K40r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K43l K43r HV74l HV74r K41l K41r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear - HV74l HV74r K41l K41r K43l K43r) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K46]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV73l HV73r K40l K40r K42l K42r) | evalEk ZA ltac:(clear - HV76l HV76r K49l K49r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV73l HV73r K40l K40r K42l K42r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24 HV73l HV73r K40l K40r K42l K42r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K49l K49r) | exact (conj K49l K49r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33 HV74l HV74r K41l K41r K43l K43r) | evalEk ZA ltac:(clear - HV75l HV75r K51l K51r) | clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33 HV74l HV74r K41l K41r K43l K43r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33 HV74l HV74r K41l K41r K43l K43r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K51l K51r) | exact (conj K51l K51r)]. }
    apply Forall_nil. }
  destruct (Pv5G7i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G7i.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 376) <= bv_unsigned a < ((V 2%nat) - 376) + 16) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5G7i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G7i.ps0) with 0x93284 in Hms. change (SR.ps_regs Pv5G7i.ps0) with (map (fun i => (i, nth i Pv5G7i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G7i.ps0) with Pv5G7i.cells0 in Hcells. unfold Pv5G7i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G7i.regs0 Pv5G7i.regs_out0 96 KS_v5G7i KS_v5G7i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7i.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5G7i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K38l K38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV63l HV63r K39l K39r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15 K16l K16r K18l K18r K19 K22 K23 K24) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G7d := LibSegY_v5G7d.
Definition KS_v5G7d : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G7d.regs0 Pv5G7d.regs_out0).
Lemma KS_v5G7d_ok : BG.kept_ok 96 Pv5G7d.regs0 Pv5G7d.regs_out0 KS_v5G7d = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma v5G7d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 20) = Z_to_bv 64 ((V 73%nat) + 1) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (V 63%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 400) + 400 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 400)) -> ((V 36%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 36%nat)) ->
  ((V 36%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 400) \/ ((V 2%nat) - 400) + 400 <= (((V 36%nat) / 8) + 2147450880)) ->
  4096 <= (V 70%nat) <= 140737488355328 -> aligned (V 70%nat) 8 -> 4104 <= ((V 70%nat) + (8 * (V 71%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 70%nat) \/ (V 70%nat) + (8 * (V 71%nat)) <= 2147446784) ->
  1 <= (V 71%nat) <= 134217728 -> L5KA.zeros_at M (((V 70%nat) / 8) + 2147450880) (V 71%nat) -> ((V 70%nat) + (8 * (V 71%nat)) <= (((V 70%nat) / 8) + 2147450880) \/ (((V 70%nat) / 8) + 2147450880) + (V 71%nat) <= (V 70%nat)) -> (((V 2%nat) - 400) + 400 <= (V 70%nat) \/ (V 70%nat) + (8 * (V 71%nat)) <= ((V 2%nat) - 400)) ->
  (((V 2%nat) - 400) + 400 <= (((V 70%nat) / 8) + 2147450880) \/ (((V 70%nat) / 8) + 2147450880) + (V 71%nat) <= ((V 2%nat) - 400)) -> 4096 <= (V 65%nat) <= 140737488355328 -> aligned (V 65%nat) 8 -> 4104 <= ((8 * (V 64%nat)) + (V 65%nat)) <= 140737479966720 ->
  (2147446784 + 17592186048512 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= 2147446784) -> 1 <= (V 64%nat) <= 134217728 -> L5KA.zeros_at M (((V 65%nat) / 8) + 2147450880) (V 64%nat) -> ((V 65%nat) + (8 * (V 64%nat)) <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= (V 65%nat)) ->
  (((V 2%nat) - 400) + 400 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= ((V 2%nat) - 400)) -> L5.u8_at RSEGS M (V 36%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 8) (V 72%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 70%nat) -> 4096 <= (V 70%nat) <= 140737488355328 ->
  aligned (V 70%nat) 8 -> 0 <= (V 72%nat) <= 18446744073709551615 -> 0 <= (V 63%nat) <= 18446744073709551615 -> 0 <= (V 73%nat) <= 134217727 ->
  0 <= (V 74%nat) <= 134217727 -> 1 <= ((V 71%nat) - (V 73%nat)) <= 134217728 -> 1 <= ((V 64%nat) - (V 74%nat)) <= 134217728 -> L5.u64_at RSEGS M ((V 2%nat) - 272) ((V 74%nat) + 1) ->
  L5KA.zeros_at M ((((V 2%nat) - 240) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 65%nat) -> L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 70%nat) + (8 * (V 73%nat))) (V 76%nat) ->
  0 <= (V 76%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 65%nat) + (8 * (V 74%nat))) (V 75%nat) -> 0 <= (V 75%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 376) <= bv_unsigned a < ((V 2%nat) - 376) + 16) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 376) <= i < ((V 2%nat) - 376) + 16) -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 16) -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x931d4 M) (st fx' R' 0x93284 M')
        /\ (forall x, In x KS_v5G7d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602736
        /\ getr R' (reg 10) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 36%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 74%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 602736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) (V 63%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) (((V 36%nat) / 8) + 2147450880)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV63l HV63r] [HV64l HV64r] [HV65l HV65r] [HV70l HV70r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] [HV75l HV75r] [HV76l HV76r] G1 G2 G8 G9 G20 G22 G23 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 [K16l K16r] K17 [K18l K18r] K19 [K20l K20r] K21 K22 K23 K24 [K25l K25r] K26 [K27l K27r] K28 [K29l K29r] K30 K31 K32 K33 K34 [K35l K35r] K36 K37 K38 [K39l K39r] K40 [K41l K41r] [K42l K42r] [K43l K43r] [K44l K44r] [K45l K45r] [K46l K46r] K47 K48 K49 K50 K51 [K52l K52r] K53 [K54l K54r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E Pv5G7d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G7d.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G7d.kn0).
  { unfold know_ok, Pv5G7d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV71l HV71r K20l K20r K45l K45r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | generalize K19; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV71l HV71r K20l K20r K45l K45r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV71l HV71r K20l K20r K45l K45r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV71l HV71r K20l K20r K45l K45r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | generalize K22; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | generalize K23; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r) | generalize K24; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r HV65l HV65r K25l K25r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | generalize K28; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r HV65l HV65r K25l K25r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r HV65l HV65r K25l K25r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r HV65l HV65r K25l K25r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | generalize K31; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | generalize K32; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r) | generalize K33; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K35l K35r K36) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K35l K35r K36) | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K35l K35r K36) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K35l K35r K36) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K35l K35r K36; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K36); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r K41l K41r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K43l K43r K45l K45r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K44l K44r K46l K46r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K18l K18r K19 K20l K20r K22 K23 K24 K45l K45r HV73l HV73r K43l K43r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K27l K27r K28 K29l K29r K31 K32 K33 K46l K46r HV74l HV74r K44l K44r) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear - HV74l HV74r K44l K44r K46l K46r) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K47]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K49]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV73l HV73r K43l K43r K45l K45r) | evalEk ZA ltac:(clear - HV76l HV76r K52l K52r) | clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV73l HV73r K43l K43r K45l K45r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r HV73l HV73r K43l K43r K45l K45r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33 HV74l HV74r K44l K44r K46l K46r) | evalEk ZA ltac:(clear - HV75l HV75r K54l K54r) | clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33 HV74l HV74r K44l K44r K46l K46r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV65l HV65r K25l K25r K27l K27r K28 K31 K32 K33 HV74l HV74r K44l K44r K46l K46r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_nil. }
  destruct (Pv5G7d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G7d.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 376) <= bv_unsigned a < ((V 2%nat) - 376) + 16) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5G7d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G7d.ps0) with 0x93284 in Hms. change (SR.ps_regs Pv5G7d.ps0) with (map (fun i => (i, nth i Pv5G7d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G7d.ps0) with Pv5G7d.cells0 in Hcells. unfold Pv5G7d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G7d.regs0 Pv5G7d.regs_out0 96 KS_v5G7d KS_v5G7d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7d.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5G7d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K16l K16r K18l K18r K19 K22 K23 K24 K39l K39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV63l HV63r K42l K42r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K23 K24 K32 K33) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G7b := LibSegY_v5G7b.
Definition KS_v5G7b : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G7b.regs0 Pv5G7b.regs_out0).
Lemma KS_v5G7b_ok : BG.kept_ok 96 Pv5G7b.regs0 Pv5G7b.regs_out0 KS_v5G7b = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G7b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 36%nat) -> 0 <= (V 36%nat) <= 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) (V 72%nat) -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93288 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_v5G7b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602780
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 72%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV58l HV58r] [HV72l HV72r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 [K9l K9r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 58%nat => (V 58%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pv5G7b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G7b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G7b.kn0).
  { unfold know_ok, Pv5G7b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV72l HV72r K9l K9r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  destruct (Pv5G7b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G7b.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G7b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G7b.ps0) with 0x8fca4 in Hms. change (SR.ps_regs Pv5G7b.ps0) with (map (fun i => (i, nth i Pv5G7b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G7b.ps0) with Pv5G7b.cells0 in Hcells. unfold Pv5G7b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G7b.regs0 Pv5G7b.regs_out0 96 KS_v5G7b KS_v5G7b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G7b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G7b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7b.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G7b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G7b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G7b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5G7b.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G7b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G8i := LibSegY_v5G8i.
Definition KS_v5G8i : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G8i.regs0 Pv5G8i.regs_out0).
Lemma KS_v5G8i_ok : BG.kept_ok 96 Pv5G8i.regs0 Pv5G8i.regs_out0 KS_v5G8i = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G8i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 36%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 36%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 36%nat)) ->
  ((V 36%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 36%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 368) (((V 36%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) ->
  0 <= (V 67%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 36%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  L5.u64_at RSEGS M ((V 36%nat) + 8) (V 72%nat) -> 0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9329c M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_v5G8i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602872
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 67%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 36%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV67l HV67r] [HV72l HV72r] G1 G2 G8 G9 G19 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 [K18l K18r] K19 [K20l K20r] K21 [K22l K22r] K23 K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 67%nat => (V 67%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pv5G8i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G8i.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G8i.kn0).
  { unfold know_ok, Pv5G8i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV67l HV67r K20l K20r) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K22l K22r K23) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K22l K22r K23) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K22l K22r K23) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K22l K22r K23) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K22l K22r K23; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K23); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r K25l K25r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pv5G8i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G8i.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G8i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G8i.ps0) with 0x8fca4 in Hms. change (SR.ps_regs Pv5G8i.ps0) with (map (fun i => (i, nth i Pv5G8i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G8i.ps0) with Pv5G8i.cells0 in Hcells. unfold Pv5G8i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G8i.regs0 Pv5G8i.regs_out0 96 KS_v5G8i KS_v5G8i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G8i.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G8i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G8i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G8i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G8i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K25l K25r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G8d := LibSegY_v5G8d.
Definition KS_v5G8d : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G8d.regs0 Pv5G8d.regs_out0).
Lemma KS_v5G8d_ok : BG.kept_ok 96 Pv5G8d.regs0 Pv5G8d.regs_out0 KS_v5G8d = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G8d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 36%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 8) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 36%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 36%nat)) ->
  ((V 36%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 36%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 368) (((V 36%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 67%nat) ->
  0 <= (V 67%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 36%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 8) (V 72%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 24) (V 70%nat) -> 4096 <= (V 70%nat) <= 140737488355328 -> aligned (V 70%nat) 8 ->
  0 <= (V 72%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9329c M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_v5G8d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602872
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 67%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 70%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV67l HV67r] [HV70l HV70r] [HV72l HV72r] G1 G2 G8 G9 G19 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 [K18l K18r] K19 [K20l K20r] K21 [K22l K22r] K23 K24 K25 [K26l K26r] K27 [K28l K28r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 67%nat => (V 67%nat) | 70%nat => (V 70%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pv5G8d.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G8d.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G8d.kn0).
  { unfold know_ok, Pv5G8d.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV67l HV67r K20l K20r) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K22l K22r K23) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K22l K22r K23) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K22l K22r K23) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K22l K22r K23) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K22l K22r K23; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K23); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r K28l K28r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r K26l K26r) | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV70l HV70r K26l K26r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  destruct (Pv5G8d.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G8d.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G8d.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G8d.ps0) with 0x8fca4 in Hms. change (SR.ps_regs Pv5G8d.ps0) with (map (fun i => (i, nth i Pv5G8d.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G8d.ps0) with Pv5G8d.cells0 in Hcells. unfold Pv5G8d.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G8d.regs0 Pv5G8d.regs_out0 96 KS_v5G8d KS_v5G8d_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G8d.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G8d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8d.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G8d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8d.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G8d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8d.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G8d.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K28l K28r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV70l HV70r K26l K26r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G8bi := LibSegY_v5G8bi.
Definition KS_v5G8bi : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G8bi.regs0 Pv5G8bi.regs_out0).
Lemma KS_v5G8bi_ok : BG.kept_ok 96 Pv5G8bi.regs0 Pv5G8bi.regs_out0 KS_v5G8bi = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G8bi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 35%nat) + 8) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 352) ((((V 35%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> 0 <= (V 66%nat) <= 18446744073709551615 ->
  L5.u8_at RSEGS M (V 35%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 67%nat) ->
  0 <= (V 67%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x932f8 M) (st fx' R' 0x93350 M')
        /\ (forall x, In x KS_v5G8bi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 35%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV66l HV66r] [HV67l HV67r] G1 G2 G8 G9 G20 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 [K24l K24r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 68%nat. }
  assert (HR: regs_ok E Pv5G8bi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G8bi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G8bi.kn0).
  { unfold know_ok, Pv5G8bi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K21l K21r K22) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K21l K21r K22) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K21l K21r K22) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K21l K21r K22) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K21l K21r K22; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K22); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r K24l K24r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  destruct (Pv5G8bi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G8bi.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G8bi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G8bi.ps0) with 0x93350 in Hms. change (SR.ps_regs Pv5G8bi.ps0) with (map (fun i => (i, nth i Pv5G8bi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G8bi.ps0) with Pv5G8bi.cells0 in Hcells. unfold Pv5G8bi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G8bi.regs0 Pv5G8bi.regs_out0 96 KS_v5G8bi KS_v5G8bi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G8bi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G8bi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8bi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G8bi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8bi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G8bi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV67l HV67r K24l K24r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G8bd := LibSegY_v5G8bd.
Definition KS_v5G8bd : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G8bd.regs0 Pv5G8bd.regs_out0).
Lemma KS_v5G8bd_ok : BG.kept_ok 96 Pv5G8bd.regs0 Pv5G8bd.regs_out0 KS_v5G8bd = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G8bd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 20) = Z_to_bv 64 (V 66%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 35%nat) + 8) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 352) ((((V 35%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> 0 <= (V 66%nat) <= 18446744073709551615 ->
  L5.u8_at RSEGS M (V 35%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 35%nat) + 24) (V 68%nat) -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 -> 0 <= (V 67%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x932f8 M) (st fx' R' 0x93350 M')
        /\ (forall x, In x KS_v5G8bd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 68%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] [HV60l HV60r] [HV66l HV66r] [HV67l HV67r] [HV68l HV68r] G1 G2 G8 G9 G20 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 K24 [K25l K25r] K26 [K27l K27r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pv5G8bd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G8bd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G8bd.kn0).
  { unfold know_ok, Pv5G8bd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K10 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r K21l K21r K22) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K21l K21r K22) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K21l K21r K22) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K21l K21r K22) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K21l K21r K22; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K22); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r K27l K27r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r K25l K25r) | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K10 K11 K12 K13 K14 K15; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K25l K25r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_nil. }
  destruct (Pv5G8bd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G8bd.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G8bd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G8bd.ps0) with 0x93350 in Hms. change (SR.ps_regs Pv5G8bd.ps0) with (map (fun i => (i, nth i Pv5G8bd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G8bd.ps0) with Pv5G8bd.cells0 in Hcells. unfold Pv5G8bd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G8bd.regs0 Pv5G8bd.regs_out0 96 KS_v5G8bd KS_v5G8bd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G8bd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G8bd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8bd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G8bd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G8bd.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G8bd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV67l HV67r K27l K27r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15) | evalEk' ZA Hag ltac:(clear - HV68l HV68r K25l K25r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5ADIVPG1.
