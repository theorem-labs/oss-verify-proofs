(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk Hoare AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import SumsLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import Asan_code_maxvaB AsanPlanImagesB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module MaxVAZ.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition smear1 (s k : Z) : Z := Z.lor s (Z.shiftr s k).

(* [comment removed for export] *)
Definition topset (s : Z) (lo : Z) : Prop :=
  0 <= s /\ (forall i, lo <= i <= 46 -> Z.testbit s i = true) /\ (forall i, 47 <= i -> Z.testbit s i = false).

Lemma topset_init : forall x, 2 ^ 46 <= x < 2 ^ 47 -> topset x 46.
Proof.
  intros x Hx. split; [lia|]. split.
  - intros i Hi. assert (i = 46) by lia. subst i.
    apply Z.testbit_true; [lia|]. replace (x / 2 ^ 46) with 1; [reflexivity|].
    apply Z.div_unique with (r := x - 2 ^ 46); lia.
  - intros i Hi. apply Z.testbit_false; [lia|].
    rewrite Z.div_small; [reflexivity|]. split; [lia|].
    apply Z.lt_le_trans with (m := 2 ^ 47); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma topset_step : forall s lo k, 0 <= k <= 47 - lo -> topset s lo -> lo <= 47 -> topset (smear1 s k) (Z.max 0 (lo - k)).
Proof.
  intros s lo k Hk (Hs & Hset & Hclr) Hlo. unfold smear1. split; [|split].
  - apply Z.lor_nonneg. split; [lia|]. apply Z.shiftr_nonneg. lia.
  - intros i Hi. rewrite Z.lor_spec. rewrite Z.shiftr_spec by lia.
    destruct (Z_le_gt_dec lo i) as [H|H].
    + rewrite (Hset i) by lia. reflexivity.
    + rewrite (Hset (i + k)) by lia. apply Bool.orb_true_r.
  - intros i Hi. rewrite Z.lor_spec. rewrite Z.shiftr_spec by lia.
    rewrite (Hclr i) by lia. rewrite (Hclr (i + k)) by lia. reflexivity.
Qed.

Lemma topset_full : forall s, topset s 0 -> s = 2 ^ 47 - 1.
Proof.
  intros s (Hs & Hset & Hclr). change (2 ^ 47 - 1) with (Z.pred (2 ^ 47)). rewrite <- (Z.ones_equiv 47).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 47) as [H|H].
  - rewrite Z.ones_spec_low by lia. apply Hset. lia.
  - rewrite Z.ones_spec_high by lia. apply Hclr. lia.
Qed.

(* [comment removed for export] *)
Definition smear6 (x : Z) : Z :=
  smear1 (smear1 (smear1 (smear1 (smear1 (smear1 x 1) 2) 4) 8) 16) 32.

Lemma smear47 : forall x, 2 ^ 46 <= x < 2 ^ 47 -> smear6 x = 2 ^ 47 - 1.
Proof.
  intros x Hx. unfold smear6. apply topset_full.
  pose proof (topset_init x Hx) as T0.
  pose proof (topset_step _ 46 1 ltac:(lia) T0 ltac:(lia)) as T1. change (Z.max 0 (46 - 1)) with 45 in T1.
  pose proof (topset_step _ 45 2 ltac:(lia) T1 ltac:(lia)) as T2. change (Z.max 0 (45 - 2)) with 43 in T2.
  pose proof (topset_step _ 43 4 ltac:(lia) T2 ltac:(lia)) as T3. change (Z.max 0 (43 - 4)) with 39 in T3.
  pose proof (topset_step _ 39 8 ltac:(lia) T3 ltac:(lia)) as T4. change (Z.max 0 (39 - 8)) with 31 in T4.
  pose proof (topset_step _ 31 16 ltac:(lia) T4 ltac:(lia)) as T5. change (Z.max 0 (31 - 16)) with 15 in T5.
  pose proof (topset_step _ 15 32 ltac:(lia) T5 ltac:(lia)) as T6. change (Z.max 0 (15 - 32)) with 0 in T6.
  exact T6.
Qed.
End MaxVAZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walk.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition wsm (s : word) (k : Z) : word := v_or s (v_srli s k).
Definition wsm5 (x : word) : word := wsm (wsm (wsm (wsm (wsm x 1) 2) 4) 8) 16.
Definition wsm6 (x : word) : word := wsm (wsm5 x) 32.
Definition maxva_a5 (x : word) : word := v_srli (wsm5 x) 32.

Lemma u_wsm : forall s k, (0 <= k)%Z -> bv_unsigned (wsm s k) = MaxVAZ.smear1 (bv_unsigned s) k.
Proof.
  intros s k Hk. unfold wsm, v_or, v_srli, MaxVAZ.smear1. pose proof (u64_range s) as Hs.
  assert (Hr : (0 <= Z.shiftr (bv_unsigned s) k < 2 ^ 64)%Z).
  { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.le_lt_trans with (m := bv_unsigned s); [|lia].
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    assert (1 <= 2 ^ k)%Z by (change 1%Z with (2 ^ 0)%Z; apply Z.pow_le_mono_r; lia). nia. }
  rewrite (u_Z2bv (Z.shiftr _ _)) by lia.
  apply u_Z2bv; pose proof (PropExec.Z_lor_range (bv_unsigned s) (Z.shiftr (bv_unsigned s) k) Hs Hr); lia.
Qed.

Lemma wsm6_val : forall x : word, (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z -> wsm6 x = Z_to_bv 64 140737488355327.
Proof.
  intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 (wsm6 x)). f_equal.
  unfold wsm6, wsm5. rewrite !u_wsm by lia. exact (MaxVAZ.smear47 _ Hx).
Qed.

(* [comment removed for export] *)
Theorem both_maxva_run : forall regs mem rom,
  exists regs',
    msteps SEGS (mkst regs (0x66870 : word) mem rom) (mkst regs' (0x668e0 : word) mem rom)
    /\ getr regs' 10 = wsm6 (getr regs 10)
    /\ getr regs' 11 = Z_to_bv 64 6148914691236517205
    /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
    /\ getr regs' 13 = Z_to_bv 64 1085102592571150095
    /\ getr regs' 14 = Z_to_bv 64 72340172838076673
    /\ getr regs' 15 = maxva_a5 (getr regs 10)
    /\ (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom. set (x := getr regs 10).
  eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - idtac.
    an F_66a14 D_66a14.
    an F_66a18 D_66a18.
    an F_66a1c D_66a1c.
    an F_66a20 D_66a20.
    an F_66a24 D_66a24.
    av_or F_66a28 D_66a28 (wsm x 1) ltac:(reflexivity).
    an F_66a2c D_66a2c.
    an F_66a30 D_66a30.
    an F_66a34 D_66a34.
    an F_66a38 D_66a38.
    an F_66a3c D_66a3c.
    av_or F_66a40 D_66a40 (wsm (wsm x 1) 2) ltac:(reflexivity).
    an F_66a44 D_66a44.
    an F_66a48 D_66a48.
    an F_66a4c D_66a4c.
    an F_66a50 D_66a50.
    an F_66a54 D_66a54.
    an F_66a58 D_66a58.
    an F_66a5c D_66a5c.
    an F_66a60 D_66a60.
    an F_66a64 D_66a64.
    av_or F_66a68 D_66a68 (wsm (wsm (wsm x 1) 2) 4) ltac:(reflexivity).
    an F_66a6c D_66a6c.
    av_or F_66a70 D_66a70 (wsm (wsm (wsm (wsm x 1) 2) 4) 8) ltac:(reflexivity).
    an F_66a74 D_66a74.
    av_or F_66a78 D_66a78 (wsm (wsm (wsm (wsm (wsm x 1) 2) 4) 8) 16) ltac:(reflexivity).
    an F_66a7c D_66a7c.
    av_or F_66a80 D_66a80 (wsm (wsm (wsm (wsm (wsm (wsm x 1) 2) 4) 8) 16) 32) ltac:(reflexivity).
    apply mst_refl.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity.
  - intros r H10 H11 H12 H13 H14 H15. rewrite !getr_other by congruence. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Walk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module APSXM.
Import AX2 AX2S AP APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition maxva_spec (SEGS : list Segment) (entry exit_ : Z) : Prop :=
  forall mem rom (regs : bvmap 5 word),
    2 ^ 46 <= bv_unsigned (getr regs 10%bv) < 2 ^ 47 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem rom) (mkst regs' (Z_to_bv 64 exit_) mem rom)
      /\ getr regs' 10%bv = Z_to_bv 64 140737488355327
      /\ getr regs' 11%bv = Z_to_bv 64 6148914691236517205
      /\ getr regs' 12%bv = Z_to_bv 64 3689348814741910323
      /\ getr regs' 13%bv = Z_to_bv 64 1085102592571150095
      /\ getr regs' 14%bv = Z_to_bv 64 72340172838076673
      /\ (forall r : bv 5, (ridx r < 10 \/ 15 < ridx r)%nat -> getr regs' r = getr regs r).

Section Sound.
Variable SEGS : list Segment.
Variable SC : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APSX.hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_S : nx0_sp_ok nx0.
Variable FS0 : Fs.Fs.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

Lemma ridx_eqb_lit : forall (r : bv 5) n, (n < 32)%nat -> Nat.eqb (ridx r) n = true -> r = Z_to_bv 5 (Z.of_nat n).
Proof. intros r n Hn H. apply Nat.eqb_eq in H. apply APSX.reg_of_ridx. exact H. Qed.

Lemma summary_maxva_sound :
  maxva_spec SEGS (x_maxva A) (x_maxva_k A) ->
  node1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 always (fun cs => summary_maxva A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
  unfold summary_maxva in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hgate; [discriminate|] end.
  apply orb_false_iff in Hgate as [Hpc _]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hlo' Hhi'].
  apply Z.leb_le in Hlo'. apply Z.ltb_lt in Hhi'.
  injection Hn as <-.
  destruct (APSX.w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (xlo_sound SEGS E _ (kn cs) _ _ HKN Hlo) as Hlo2.
  pose proof (xhi_sound SEGS E _ (kn cs) _ _ HKN Hhi) as Hhi2.
  pose proof (APSX.w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  assert (HX : 2 ^ 46 <= bv_unsigned (getr R 10%bv) < 2 ^ 47).
  { replace (getr R 10%bv) with (edenot E (reg cs 10)) by (symmetry; exact R10). lia. }
  destruct (SUM (Mr A argH E cs model FULL) (seg_rom SEGS) R HX)
    as (regs' & Hms & H10 & H11 & H12 & H13 & H14 & Hoth).
  set (E' := ext1 E (nxt cs) (getr regs' 15%bv)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext1_agree.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_S FS0 E E' cs R FULL model Hag Hfresh HC)) as HRE.
  eapply (APSX.call_core SEGS SC A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_S FS0
            cs E E' R FULL model T (x_maxva_k A)
            (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs))
               10 (ELit 140737488355327)) 11 (ELit 6148914691236517205)) 12 (ELit 3689348814741910323))
               13 (ELit 1085102592571150095)) 14 (ELit 72340172838076673)) 15 (EVar (nxt cs)))
            (kn cs) (S (nxt cs)) regs' (Mr A argH E cs model FULL) HC Hfresh Hag).
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    intros r. specialize (HRE r). unfold sr_get in *.
    destruct (bv_eqb r 0) eqn:Hr0.
    { assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
      rewrite <- HRE. apply Hoth. left. change (ridx 0%bv) with 0%nat. lia. }
    rewrite !nth_sr_upd.
    destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (ridx_eqb_lit r 15 ltac:(lia)) in E15; subst r; cbn [edenot]; unfold E'; rewrite ext1_at; reflexivity|].
    destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (ridx_eqb_lit r 14 ltac:(lia)) in E14; subst r; exact H14|].
    destruct (Nat.eqb (ridx r) 13) eqn:E13; [apply (ridx_eqb_lit r 13 ltac:(lia)) in E13; subst r; exact H13|].
    destruct (Nat.eqb (ridx r) 12) eqn:E12; [apply (ridx_eqb_lit r 12 ltac:(lia)) in E12; subst r; exact H12|].
    destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (ridx_eqb_lit r 11 ltac:(lia)) in E11; subst r; exact H11|].
    destruct (Nat.eqb (ridx r) 10) eqn:E10; [apply (ridx_eqb_lit r 10 ltac:(lia)) in E10; subst r; exact H10|].
    rewrite <- HRE. change (nth (ridx r) (s_regs (a_ss cs)) (ELit 0)) with (reg cs (ridx r)).
    apply Hoth. apply Nat.eqb_neq in E10. apply Nat.eqb_neq in E11. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E13.
    apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E15. lia.
  - (* [comment removed for export] *)
    eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Theorem node_x_sound_XMaxVA :
  maxva_spec SEGS (x_maxva A) (x_maxva_k A) -> x_stmt SEGS SC A nx0 LIMIT SINV argH FS0 XMaxVA.
Proof. intros SUM args. exact (summary_maxva_sound SUM). Qed.
End Sound.
End APSXM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.

Lemma both_maxva_spec : APSXM.maxva_spec BSEGS (AP.x_maxva BOTH5) (AP.x_maxva_k BOTH5).
Proof.
  intros mem rom regs Hx.
  destruct (both_maxva_run regs mem rom) as (regs' & Hms & H10 & H11 & H12 & H13 & H14 & _ & Hoth).
  exists regs'. split; [|split; [|split; [exact H11|split; [exact H12|split; [exact H13|split; [exact H14|]]]]]].
  - replace (Z_to_bv 64 (AP.x_maxva BOTH5)) with (0x66870%bv : word) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 (AP.x_maxva_k BOTH5)) with (0x668e0%bv : word) by (apply bv_eq; reflexivity).
    exact Hms.
  - rewrite H10. apply wsm6_val. exact Hx.
  - intros r Hr. apply Hoth; intros ->;
      [ change (AX2.ridx 10%bv) with 10%nat in Hr | change (AX2.ridx 11%bv) with 11%nat in Hr
      | change (AX2.ridx 12%bv) with 12%nat in Hr | change (AX2.ridx 13%bv) with 13%nat in Hr
      | change (AX2.ridx 14%bv) with 14%nat in Hr | change (AX2.ridx 15%bv) with 15%nat in Hr ]; lia.
Qed.

Section AsanNodes.
Variable SC : SpuriousCfg.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_S : APS.nx0_sp_ok nx0.
Variable FS0 : Fs.Fs.

Theorem both_node_x_sound_XMaxVA : APS.x_stmt BSEGS SC BOTH5 nx0 LIMIT SINV argH FS0 AP.XMaxVA.
Proof.
  eapply APSXM.node_x_sound_XMaxVA; try eassumption.
  - exact both_wx.
  - exact both_in_hull.
  - exact both_hull_ok.
  - exact both_maxva_spec.
Qed.
End AsanNodes.
