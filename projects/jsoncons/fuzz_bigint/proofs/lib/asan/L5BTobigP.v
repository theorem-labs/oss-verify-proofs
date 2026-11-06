(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Bo0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_tqA LibSegY_tqB LibSegY_tqCm LibSegY_tqCl LibSegY_tqCh LibSegY_tqD LibSegY_trA LibSegY_trB LibSegY_trCm LibSegY_trCl LibSegY_trCh LibSegY_trD.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ATBP.
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
Module PtqA := LibSegY_tqA.
Definition KS_tqA : list nat := Eval vm_compute in (BG.kept_list 64 PtqA.regs0 PtqA.regs_out0).
Lemma KS_tqA_ok : BG.kept_ok 64 PtqA.regs0 PtqA.regs_out0 KS_tqA = true. Proof. vm_compute. reflexivity. Qed.
Lemma tqA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8ec9c M) (st fx' R' 0x8ed0c M')
        /\ (forall x, In x KS_tqA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 22).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV36l HV36r] [HV37l HV37r] G2 G10 G11 G12 G13 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PtqA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtqA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtqA.kn0).
  { unfold know_ok, PtqA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtqA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtqA.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtqA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtqA.ps0) with 0x8ed0c in Hms. change (SR.ps_regs PtqA.ps0) with (map (fun i => (i, nth i PtqA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtqA.ps0) with PtqA.cells0 in Hcells. unfold PtqA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtqA.regs0 PtqA.regs_out0 64 KS_tqA KS_tqA_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtqA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtqA.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtqB := LibSegY_tqB.
Definition KS_tqB : list nat := Eval vm_compute in (BG.kept_list 64 PtqB.regs0 PtqB.regs_out0).
Lemma KS_tqB_ok : BG.kept_ok 64 PtqB.regs0 PtqB.regs_out0 KS_tqB = true. Proof. vm_compute. reflexivity. Qed.
Lemma tqB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 1 <= (V 34%nat) <= 67108863 -> 4096 <= (V 33%nat) <= 140737479966720 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8ec9c M) (st fx' R' 0x8ecc8 M')
        /\ (forall x, In x KS_tqB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 33%nat) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] G2 G10 G11 G12 G13 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PtqB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtqB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtqB.kn0).
  { unfold know_ok, PtqB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (PtqB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtqB.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtqB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtqB.ps0) with 0x8ecc8 in Hms. change (SR.ps_regs PtqB.ps0) with (map (fun i => (i, nth i PtqB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtqB.ps0) with PtqB.cells0 in Hcells. unfold PtqB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtqB.regs0 PtqB.regs_out0 64 KS_tqB KS_tqB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtqB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtqB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtqB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PtqB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PtqB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PtqB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtqCm := LibSegY_tqCm.
Definition KS_tqCm : list nat := Eval vm_compute in (BG.kept_list 64 PtqCm.regs0 PtqCm.regs_out0).
Lemma KS_tqCm_ok : BG.kept_ok 64 PtqCm.regs0 PtqCm.regs_out0 KS_tqCm = true. Proof. vm_compute. reflexivity. Qed.
Lemma tqCm_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 37%nat) -> getr R (reg 15) = Z_to_bv 64 (V 60%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737479966720 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) ->
  45 <= (V 56%nat) <= 45 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 1 <= ((V 2%nat) - 16)) -> 1 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8ecd0 M) (st fx' R' 0x8ed28 M')
        /\ (forall x, In x KS_tqCm -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 584956
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 45).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV56l HV56r] [HV59l HV59r] [HV60l HV60r] G2 G10 G11 G12 G13 G14 G15 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 56%nat => (V 56%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtqCm.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtqCm.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtqCm.kn0).
  { unfold know_ok, PtqCm.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | clear - HV33l HV33r K6l K6r K9; lia | clear - HV33l HV33r K6l K6r K9; lia | byte_tac ltac:(clear - HV56l HV56r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (PtqCm.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtqCm.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtqCm.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtqCm.ps0) with 0x8ed28 in Hms. change (SR.ps_regs PtqCm.ps0) with (map (fun i => (i, nth i PtqCm.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtqCm.ps0) with PtqCm.cells0 in Hcells. unfold PtqCm.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtqCm.regs0 PtqCm.regs_out0 64 KS_tqCm KS_tqCm_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtqCm.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtqCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqCm.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtqCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqCm.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtqCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqCm.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtqCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtqCm.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PtqCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtqCl := LibSegY_tqCl.
Definition KS_tqCl : list nat := Eval vm_compute in (BG.kept_list 64 PtqCl.regs0 PtqCl.regs_out0).
Lemma KS_tqCl_ok : BG.kept_ok 64 PtqCl.regs0 PtqCl.regs_out0 KS_tqCl = true. Proof. vm_compute. reflexivity. Qed.
Lemma tqCl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 37%nat) -> getr R (reg 15) = Z_to_bv 64 (V 60%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737479966720 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) ->
  0 <= (V 56%nat) <= 44 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 1 <= ((V 2%nat) - 16)) -> 1 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8ecd0 M) (st fx' R' 0x8ed28 M')
        /\ (forall x, In x KS_tqCl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 584956
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 45).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV56l HV56r] [HV59l HV59r] [HV60l HV60r] G2 G10 G11 G12 G13 G14 G15 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 56%nat => (V 56%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtqCl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtqCl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtqCl.kn0).
  { unfold know_ok, PtqCl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | clear - HV33l HV33r K6l K6r K9; lia | clear - HV33l HV33r K6l K6r K9; lia | byte_tac ltac:(clear - HV56l HV56r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (PtqCl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtqCl.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtqCl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtqCl.ps0) with 0x8ed28 in Hms. change (SR.ps_regs PtqCl.ps0) with (map (fun i => (i, nth i PtqCl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtqCl.ps0) with PtqCl.cells0 in Hcells. unfold PtqCl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtqCl.regs0 PtqCl.regs_out0 64 KS_tqCl KS_tqCl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtqCl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtqCl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqCl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtqCl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtqCl.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PtqCl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtqCh := LibSegY_tqCh.
Definition KS_tqCh : list nat := Eval vm_compute in (BG.kept_list 64 PtqCh.regs0 PtqCh.regs_out0).
Lemma KS_tqCh_ok : BG.kept_ok 64 PtqCh.regs0 PtqCh.regs_out0 KS_tqCh = true. Proof. vm_compute. reflexivity. Qed.
Lemma tqCh_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 37%nat) -> getr R (reg 15) = Z_to_bv 64 (V 60%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737479966720 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) ->
  46 <= (V 56%nat) <= 255 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 1 <= ((V 2%nat) - 16)) -> 1 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8ecd0 M) (st fx' R' 0x8ed28 M')
        /\ (forall x, In x KS_tqCh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 584956
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 45).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV56l HV56r] [HV59l HV59r] [HV60l HV60r] G2 G10 G11 G12 G13 G14 G15 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 56%nat => (V 56%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtqCh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtqCh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtqCh.kn0).
  { unfold know_ok, PtqCh.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | clear - HV33l HV33r K6l K6r K9; lia | clear - HV33l HV33r K6l K6r K9; lia | byte_tac ltac:(clear - HV56l HV56r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (PtqCh.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtqCh.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtqCh.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtqCh.ps0) with 0x8ed28 in Hms. change (SR.ps_regs PtqCh.ps0) with (map (fun i => (i, nth i PtqCh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtqCh.ps0) with PtqCh.cells0 in Hcells. unfold PtqCh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtqCh.regs0 PtqCh.regs_out0 64 KS_tqCh KS_tqCh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtqCh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtqCh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtqCh.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtqCh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtqCh.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PtqCh.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtqD := LibSegY_tqD.
Definition KS_tqD : list nat := Eval vm_compute in (BG.kept_list 64 PtqD.regs0 PtqD.regs_out0).
Lemma KS_tqD_ok : BG.kept_ok 64 PtqD.regs0 PtqD.regs_out0 KS_tqD = true. Proof. vm_compute. reflexivity. Qed.
Lemma tqD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 61%nat) -> getr R (reg 11) = Z_to_bv 64 (V 62%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> 0 <= (V 62%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8ecfc M) (st fx' R' 0x8ed0c M')
        /\ (forall x, In x KS_tqD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)).
Proof.
  intros [HV2l HV2r] [HV42l HV42r] [HV58l HV58r] [HV61l HV61r] [HV62l HV62r] G1 G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 42%nat => (V 42%nat) | 58%nat => (V 58%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtqD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtqD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtqD.kn0).
  { unfold know_ok, PtqD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (PtqD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtqD.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtqD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtqD.ps0) with 0x8ed0c in Hms. change (SR.ps_regs PtqD.ps0) with (map (fun i => (i, nth i PtqD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtqD.ps0) with PtqD.cells0 in Hcells. unfold PtqD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtqD.regs0 PtqD.regs_out0 64 KS_tqD KS_tqD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtqD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtqD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtqD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtqD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtrA := LibSegY_trA.
Definition KS_trA : list nat := Eval vm_compute in (BG.kept_list 64 PtrA.regs0 PtrA.regs_out0).
Lemma KS_trA_ok : BG.kept_ok 64 PtrA.regs0 PtrA.regs_out0 KS_trA = true. Proof. vm_compute. reflexivity. Qed.
Lemma trA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92034 M) (st fx' R' 0x920a8 M')
        /\ (forall x, In x KS_trA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 22).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV36l HV36r] [HV37l HV37r] G2 G10 G11 G12 G13 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PtrA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtrA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtrA.kn0).
  { unfold know_ok, PtrA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PtrA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtrA.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtrA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtrA.ps0) with 0x920a8 in Hms. change (SR.ps_regs PtrA.ps0) with (map (fun i => (i, nth i PtrA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtrA.ps0) with PtrA.cells0 in Hcells. unfold PtrA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtrA.regs0 PtrA.regs_out0 64 KS_trA KS_trA_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtrA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtrB := LibSegY_trB.
Definition KS_trB : list nat := Eval vm_compute in (BG.kept_list 64 PtrB.regs0 PtrB.regs_out0).
Lemma KS_trB_ok : BG.kept_ok 64 PtrB.regs0 PtrB.regs_out0 KS_trB = true. Proof. vm_compute. reflexivity. Qed.
Lemma trB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 1 <= (V 34%nat) <= 67108863 -> 4096 <= (V 33%nat) <= 140737479966720 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92034 M) (st fx' R' 0x9205c M')
        /\ (forall x, In x KS_trB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] G2 G10 G11 G12 G13 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PtrB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtrB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtrB.kn0).
  { unfold know_ok, PtrB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (PtrB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtrB.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtrB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtrB.ps0) with 0x9205c in Hms. change (SR.ps_regs PtrB.ps0) with (map (fun i => (i, nth i PtrB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtrB.ps0) with PtrB.cells0 in Hcells. unfold PtrB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtrB.regs0 PtrB.regs_out0 64 KS_trB KS_trB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtrB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PtrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PtrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtrCm := LibSegY_trCm.
Definition KS_trCm : list nat := Eval vm_compute in (BG.kept_list 64 PtrCm.regs0 PtrCm.regs_out0).
Lemma KS_trCm_ok : BG.kept_ok 64 PtrCm.regs0 PtrCm.regs_out0 KS_trCm = true. Proof. vm_compute. reflexivity. Qed.
Lemma trCm_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 60%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737479966720 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) ->
  45 <= (V 56%nat) <= 45 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 1 <= ((V 2%nat) - 16)) -> 1 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92064 M) (st fx' R' 0x8ed28 M')
        /\ (forall x, In x KS_trCm -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 598168
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 9)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV56l HV56r] [HV59l HV59r] [HV60l HV60r] G2 G10 G11 G12 G13 G14 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 56%nat => (V 56%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtrCm.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtrCm.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtrCm.kn0).
  { unfold know_ok, PtrCm.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | clear - HV33l HV33r K6l K6r K9; lia | clear - HV33l HV33r K6l K6r K9; lia | byte_tac ltac:(clear - HV56l HV56r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (PtrCm.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtrCm.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtrCm.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtrCm.ps0) with 0x8ed28 in Hms. change (SR.ps_regs PtrCm.ps0) with (map (fun i => (i, nth i PtrCm.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtrCm.ps0) with PtrCm.cells0 in Hcells. unfold PtrCm.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtrCm.regs0 PtrCm.regs_out0 64 KS_trCm KS_trCm_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtrCm.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtrCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrCm.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtrCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrCm.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtrCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrCm.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtrCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtrCm.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PtrCm.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtrCl := LibSegY_trCl.
Definition KS_trCl : list nat := Eval vm_compute in (BG.kept_list 64 PtrCl.regs0 PtrCl.regs_out0).
Lemma KS_trCl_ok : BG.kept_ok 64 PtrCl.regs0 PtrCl.regs_out0 KS_trCl = true. Proof. vm_compute. reflexivity. Qed.
Lemma trCl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 60%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737479966720 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) ->
  0 <= (V 56%nat) <= 44 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 1 <= ((V 2%nat) - 16)) -> 1 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92064 M) (st fx' R' 0x8ed28 M')
        /\ (forall x, In x KS_trCl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 598168
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 10)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV56l HV56r] [HV59l HV59r] [HV60l HV60r] G2 G10 G11 G12 G13 G14 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 56%nat => (V 56%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtrCl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtrCl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtrCl.kn0).
  { unfold know_ok, PtrCl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | clear - HV33l HV33r K6l K6r K9; lia | clear - HV33l HV33r K6l K6r K9; lia | byte_tac ltac:(clear - HV56l HV56r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (PtrCl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtrCl.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtrCl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtrCl.ps0) with 0x8ed28 in Hms. change (SR.ps_regs PtrCl.ps0) with (map (fun i => (i, nth i PtrCl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtrCl.ps0) with PtrCl.cells0 in Hcells. unfold PtrCl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtrCl.regs0 PtrCl.regs_out0 64 KS_trCl KS_trCl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtrCl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtrCl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrCl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtrCl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtrCl.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PtrCl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtrCh := LibSegY_trCh.
Definition KS_trCh : list nat := Eval vm_compute in (BG.kept_list 64 PtrCh.regs0 PtrCh.regs_out0).
Lemma KS_trCh_ok : BG.kept_ok 64 PtrCh.regs0 PtrCh.regs_out0 KS_trCh = true. Proof. vm_compute. reflexivity. Qed.
Lemma trCh_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) -> getr R (reg 14) = Z_to_bv 64 (V 60%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737479966720 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) ->
  46 <= (V 56%nat) <= 255 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 1 <= ((V 2%nat) - 16)) -> 1 <= (V 34%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92064 M) (st fx' R' 0x8ed28 M')
        /\ (forall x, In x KS_trCh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 598168
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 10)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV56l HV56r] [HV59l HV59r] [HV60l HV60r] G2 G10 G11 G12 G13 G14 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 56%nat => (V 56%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtrCh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtrCh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtrCh.kn0).
  { unfold know_ok, PtrCh.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | clear - HV33l HV33r K6l K6r K9; lia | clear - HV33l HV33r K6l K6r K9; lia | byte_tac ltac:(clear - HV56l HV56r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  destruct (PtrCh.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtrCh.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtrCh.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtrCh.ps0) with 0x8ed28 in Hms. change (SR.ps_regs PtrCh.ps0) with (map (fun i => (i, nth i PtrCh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtrCh.ps0) with PtrCh.cells0 in Hcells. unfold PtrCh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtrCh.regs0 PtrCh.regs_out0 64 KS_trCh KS_trCh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtrCh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtrCh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtrCh.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtrCh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtrCh.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PtrCh.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtrD := LibSegY_trD.
Definition KS_trD : list nat := Eval vm_compute in (BG.kept_list 64 PtrD.regs0 PtrD.regs_out0).
Lemma KS_trD_ok : BG.kept_ok 64 PtrD.regs0 PtrD.regs_out0 KS_trD = true. Proof. vm_compute. reflexivity. Qed.
Lemma trD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 10) = Z_to_bv 64 (V 61%nat) -> getr R (reg 11) = Z_to_bv 64 (V 62%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> 0 <= (V 62%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92098 M) (st fx' R' 0x920a8 M')
        /\ (forall x, In x KS_trD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)).
Proof.
  intros [HV2l HV2r] [HV42l HV42r] [HV58l HV58r] [HV61l HV61r] [HV62l HV62r] G1 G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 42%nat => (V 42%nat) | 58%nat => (V 58%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtrD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtrD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtrD.kn0).
  { unfold know_ok, PtrD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  destruct (PtrD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtrD.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtrD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtrD.ps0) with 0x920a8 in Hms. change (SR.ps_regs PtrD.ps0) with (map (fun i => (i, nth i PtrD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtrD.ps0) with PtrD.cells0 in Hcells. unfold PtrD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtrD.regs0 PtrD.regs_out0 64 KS_trD KS_trD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtrD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtrD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ATBP.
