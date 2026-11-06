(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg AsanPlanSoundSumsCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanBySizeLogSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesSL.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX APSXC.
Unset Lia Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition sl_clob (r : bv 5) : bool :=
  (bv_eqb r 11%bv || bv_eqb r 12%bv || bv_eqb r 14%bv || bv_eqb r 15%bv || bv_eqb r 16%bv || bv_eqb r 19%bv)%bool.

(* [comment removed for export] *)
Definition sizelog_spec (SEGS : list Segment) (T : SLN.sltab) : Prop :=
  forall mem (regs : bvmap 5 word) (x m c : Z) (bs : list byte) (w : word),
    0 <= m <= 63 -> 2 ^ m <= x < 2 ^ (m + 1) -> x < 2 ^ 64 ->
    getr regs 18%bv = Z_to_bv 64 x ->
    0 <= c -> c + 8 <= 2 ^ 64 -> v_addi (getr regs 9%bv) 48 = Z_to_bv 64 c ->
    rdn SEGS mem (Z_to_bv 64 c) 8 = Some bs -> bytes_le_to_Z bs = bv_unsigned w ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (SLN.sl_entry T)) mem (seg_rom SEGS))
                  (mkst regs' (Z_to_bv 64 (SLN.sl_exit T)) mem (seg_rom SEGS))
      /\ getr regs' 19%bv = Z_to_bv 64 (63 - m)
      /\ getr regs' 11%bv = Z_to_bv 64 (SLN.sl_prod m)
      /\ getr regs' 12%bv = Z_to_bv 64 0x0101010101010101
      /\ getr regs' 14%bv = w
      /\ getr regs' 15%bv = Z_to_bv 64 0x0F0F0F0F0F0F0F0F
      /\ getr regs' 16%bv = Z_to_bv 64 0x01010101
      /\ (forall r, sl_clob r = false -> getr regs' r = getr regs r).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable T : SLN.sltab.
Hypothesis SLSPEC : sizelog_spec SEGS T.
Hypothesis BSSPEC : bysizelog_spec SEGS (SLN.bs_entry T) (SLN.bs_exit T).

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

Lemma nth_sl_regs : forall sr m cell i,
  nth i (SLN.sl_regs sr m cell) (ELit 0) =
    if Nat.eqb i 16 then ELit 0x01010101 else if Nat.eqb i 15 then ELit 0x0F0F0F0F0F0F0F0F else if Nat.eqb i 14 then cell
    else if Nat.eqb i 12 then ELit 0x0101010101010101 else if Nat.eqb i 11 then ELit (SLN.sl_prod m) else if Nat.eqb i 19 then ELit (63 - m)
    else nth i sr (ELit 0).
Proof.
  intros sr m cell i. unfold SLN.sl_regs. rewrite !nth_sr_upd.
  destruct (Nat.eqb i 16); [reflexivity|]. destruct (Nat.eqb i 15); [reflexivity|]. destruct (Nat.eqb i 14); [reflexivity|].
  destruct (Nat.eqb i 12); [reflexivity|]. destruct (Nat.eqb i 11); [reflexivity|]. destruct (Nat.eqb i 19); reflexivity.
Qed.

Lemma nth_sl_regs_r : forall sr v cell i,
  nth i (SLN.sl_regs_r sr v cell) (ELit 0) =
    if Nat.eqb i 16 then ELit 0x01010101 else if Nat.eqb i 15 then ELit 0x0F0F0F0F0F0F0F0F else if Nat.eqb i 14 then cell
    else if Nat.eqb i 12 then ELit 0x0101010101010101 else if Nat.eqb i 11 then EVar (S v) else if Nat.eqb i 19 then EVar v
    else nth i sr (ELit 0).
Proof.
  intros sr v cell i. unfold SLN.sl_regs_r. rewrite !nth_sr_upd.
  destruct (Nat.eqb i 16); [reflexivity|]. destruct (Nat.eqb i 15); [reflexivity|]. destruct (Nat.eqb i 14); [reflexivity|].
  destruct (Nat.eqb i 12); [reflexivity|]. destruct (Nat.eqb i 11); [reflexivity|]. destruct (Nat.eqb i 19); reflexivity.
Qed.

Theorem node_sizelog_sound :
  APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (SLN.node_sizelog SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold SLN.node_sizelog in Hn.
  destruct (Z.eqb (pc cs) (SLN.sl_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (split_lit (eaddz (reg cs 9) 48)) as [cb ck] eqn:Hsc.
  destruct (xlo (kn cs) (reg cs 18)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 18)) as [hi|] eqn:Hhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hflc]. apply andb_prop in Hcond as [Hcond Hhi64].
  apply andb_prop in Hcond as [Hlo1 Hlohi].
  apply Z.leb_le in Hlo1. apply Z.leb_le in Hlohi. apply Z.ltb_lt in Hhi64.
  destruct (know_lookup SEGS (kn cs) cb ck 8 false [] []) as [v0 scs hs|scs hs|] eqn:HL1; try discriminate Hn.
  destruct scs; [|discriminate Hn].
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 18 HC ltac:(lia)) as R18.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hlo) as Hlo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hhi) as Hhi2.
  set (xw := edenot E (reg cs 18)) in *. set (x := bv_unsigned xw) in *.
  set (m := Z.log2 x).
  pose proof (Z.log2_spec x ltac:(lia)) as [Hm1 Hm2]. fold m in Hm1, Hm2.
  pose proof (Z.log2_nonneg x) as Hm0. fold m in Hm0.
  pose proof (Z.log2_le_mono lo x ltac:(lia)) as HmL. pose proof (Z.log2_le_mono x hi ltac:(lia)) as HmH. fold m in HmL, HmH.
  assert (Hm63 : m <= 63).
  { destruct (Z.le_gt_cases m 63) as [|Hgt]; [assumption|]. exfalso.
    assert (2 ^ 64 <= 2 ^ m) by (apply Z.pow_le_mono_r; lia). unfold two64 in Hhi64. pose proof (u64_range xw). lia. }
  assert (HxW : Z_to_bv 64 x = xw) by (apply Z_to_bv_bv_unsigned).
  pose proof (u64_range xw) as Hxr. fold x in Hxr.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ cb ck Hsc) as Hcw.
  destruct (w_flat_x_sound SEGS E M (kn cs) cb ck (ELit 8) HKN Hflc) as (Clo & Chi & _).
  replace (bv_unsigned (edenot E (ELit 8))) with 8 in Chi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  set (c := estart E (SA cb ck)) in *.
  pose proof (know_lookup_sound SEGS E M (kn cs) cb ck 8 false [] [] HKN ltac:(lia) ltac:(lia)) as XL.
  rewrite HL1 in XL. destruct (XL ltac:(constructor) ltac:(unfold flat; fold c; lia)) as (bs & Hrd & Hlen & Hv). clear XL.
  rewrite adenot_SA in Hrd. fold c in Hrd.
  assert (Hc9 : v_addi (getr R 9%bv) 48 = Z_to_bv 64 c).
  { replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in R9 by (apply bv_eq; reflexivity). rewrite R9.
    unfold eaddz in Hcw. rewrite mkAlu_denot, alu_add in Hcw. unfold v_add in Hcw. cbn [edenot] in Hcw.
    rewrite (u64_lit 48) in Hcw by lia. unfold v_addi. rewrite Hcw. unfold c, estart. cbn [a_base a_off]. reflexivity. }
  set (w := edenot E (extK (kn cs) v0)).
  assert (Hbs : bytes_le_to_Z bs = bv_unsigned w).
  { unfold w. rewrite (extK_denot SEGS E M (kn cs) v0 HKN), <- Hv. cbn [extz].
    pose proof (bytes_le_to_Z_bound bs) as Hbr. rewrite Hlen in Hbr.
    rewrite u64_lit; [reflexivity |]. change (2 ^ 64) with (2 ^ (8 * Z.of_nat 8)). lia. }
  (* [comment removed for export] *)
  replace (Z_to_bv 5 (Z.of_nat 18)) with (18%bv : bv 5) in R18 by (apply bv_eq; reflexivity).
  destruct (SLSPEC M R x m c bs w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R18; fold xw; symmetry; exact HxW)
              ltac:(lia) ltac:(lia) Hc9 Hrd Hbs) as (regs' & Hms & H19 & H11 & H12 & H14 & H15 & H16 & Hother).
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
  assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
  { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
    exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
  assert (RX : forall r n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> Nat.eqb (ridx r) n = true -> r = rr).
  { intros r n rr Hn' Hrb EQ1. apply Nat.eqb_eq in EQ1. rewrite (reg_of_ridx r n EQ1). apply bv_eq.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrb. }
  destruct (Z.eqb (Z.log2 lo) (Z.log2 hi)) eqn:Hmsb.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in Hmsb. injection Hn as <-.
    assert (Hmm : Z.log2 lo = m) by lia.
    assert (Hag : env_agree (nxt cs) E E) by (split; [intros; reflexivity | reflexivity]).
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
              cs E E R FULL model TT (SLN.sl_exit T) (SLN.sl_regs (s_regs (a_ss cs)) (Z.log2 lo) (extK (kn cs) v0)) (kn cs) (nxt cs) regs' M HC Hfresh Hag).
    + rewrite Hpc. exact Hms.
    + apply regs_ok_pointwise. intros r Hr0. rewrite nth_sl_regs, Hmm.
      destruct (Nat.eqb (ridx r) 16) eqn:E16; [apply (RX r 16%nat 16%bv ltac:(lia) eq_refl) in E16; subst r; cbn [edenot]; exact H16|].
      destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (RX r 15%nat 15%bv ltac:(lia) eq_refl) in E15; subst r; cbn [edenot]; exact H15|].
      destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (RX r 14%nat 14%bv ltac:(lia) eq_refl) in E14; subst r; rewrite H14; reflexivity|].
      destruct (Nat.eqb (ridx r) 12) eqn:E12; [apply (RX r 12%nat 12%bv ltac:(lia) eq_refl) in E12; subst r; cbn [edenot]; exact H12|].
      destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (RX r 11%nat 11%bv ltac:(lia) eq_refl) in E11; subst r; cbn [edenot]; exact H11|].
      destruct (Nat.eqb (ridx r) 19) eqn:E19; [apply (RX r 19%nat 19%bv ltac:(lia) eq_refl) in E19; subst r; cbn [edenot]; rewrite H19; reflexivity|].
      assert (N11 : r <> 11%bv) by (intros ->; cbv in E11; discriminate E11).
      assert (N12 : r <> 12%bv) by (intros ->; cbv in E12; discriminate E12).
      assert (N14 : r <> 14%bv) by (intros ->; cbv in E14; discriminate E14).
      assert (N15 : r <> 15%bv) by (intros ->; cbv in E15; discriminate E15).
      assert (N16 : r <> 16%bv) by (intros ->; cbv in E16; discriminate E16).
      assert (N19 : r <> 19%bv) by (intros ->; cbv in E19; discriminate E19).
      rewrite Hother; [ apply HRr; exact Hr0 |].
      unfold sl_clob. rewrite (bv_eqb_neq _ _ N11), (bv_eqb_neq _ _ N12), (bv_eqb_neq _ _ N14), (bv_eqb_neq _ _ N15),
        (bv_eqb_neq _ _ N16), (bv_eqb_neq _ _ N19). reflexivity.
    + exact HKN.
    + intros R' FULL' model' HC' Hfs'. apply (Hk E R' FULL' model'); [| exact HC' | exact Hfs'].
      split; (split; [intros; reflexivity | reflexivity]).
  - (* [comment removed for export] *)
    destruct (erange (kn cs) (extK (kn cs) v0)) as [[c1 c2]|] eqn:Hec; [|discriminate Hn].
    destruct (Z.eqb c1 c2) eqn:Hc12; [|discriminate Hn]. apply Z.eqb_eq in Hc12. subst c2.
    pose proof (erange_sound SEGS E M (kn cs) _ c1 c1 HKN Hec) as Hwc. fold w in Hwc.
    assert (Hwlit : w = Z_to_bv 64 c1) by (rewrite <- (Z_to_bv_bv_unsigned 64 w); f_equal; lia).
    injection Hn as <-.
    set (VALS := [Z_to_bv 64 (63 - m); Z_to_bv 64 (SLN.sl_prod m)]).
    set (E' := ext_list E (nxt cs) VALS).
    pose proof (ext_list_agree E (nxt cs) VALS) as Hag. fold E' in Hag.
    pose proof (ext_list_at E (nxt cs) VALS 0 ltac:(cbn; lia)) as X0. fold E' in X0. cbn [nth VALS] in X0.
    pose proof (ext_list_at E (nxt cs) VALS 1 ltac:(cbn; lia)) as X1. fold E' in X1. cbn [nth VALS] in X1.
    replace (nxt cs + 0)%nat with (nxt cs) in X0 by lia. replace (nxt cs + 1)%nat with (S (nxt cs)) in X1 by lia.
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
              cs E E' R FULL model TT (SLN.sl_exit T) (SLN.sl_regs_r (s_regs (a_ss cs)) (nxt cs) (ELit c1))
              (KRange (EVar (nxt cs)) (63 - Z.log2 hi) (63 - Z.log2 lo) :: kn cs) (S (S (nxt cs))) regs' M HC Hfresh Hag).
    + rewrite Hpc. exact Hms.
    + apply regs_ok_pointwise. intros r Hr0. rewrite nth_sl_regs_r.
      assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i (s_regs (a_ss cs)) (ELit 0)) = edenot E (nth i (s_regs (a_ss cs)) (ELit 0))).
      { intros i Hi. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
      destruct (Nat.eqb (ridx r) 16) eqn:E16; [apply (RX r 16%nat 16%bv ltac:(lia) eq_refl) in E16; subst r; cbn [edenot]; exact H16|].
      destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (RX r 15%nat 15%bv ltac:(lia) eq_refl) in E15; subst r; cbn [edenot]; exact H15|].
      destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (RX r 14%nat 14%bv ltac:(lia) eq_refl) in E14; subst r; cbn [edenot]; rewrite H14; exact Hwlit|].
      destruct (Nat.eqb (ridx r) 12) eqn:E12; [apply (RX r 12%nat 12%bv ltac:(lia) eq_refl) in E12; subst r; cbn [edenot]; exact H12|].
      destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (RX r 11%nat 11%bv ltac:(lia) eq_refl) in E11; subst r; cbn [edenot]; rewrite X1; exact H11|].
      destruct (Nat.eqb (ridx r) 19) eqn:E19; [apply (RX r 19%nat 19%bv ltac:(lia) eq_refl) in E19; subst r; cbn [edenot]; rewrite X0; exact H19|].
      assert (N11 : r <> 11%bv) by (intros ->; cbv in E11; discriminate E11).
      assert (N12 : r <> 12%bv) by (intros ->; cbv in E12; discriminate E12).
      assert (N14 : r <> 14%bv) by (intros ->; cbv in E14; discriminate E14).
      assert (N15 : r <> 15%bv) by (intros ->; cbv in E15; discriminate E15).
      assert (N16 : r <> 16%bv) by (intros ->; cbv in E16; discriminate E16).
      assert (N19 : r <> 19%bv) by (intros ->; cbv in E19; discriminate E19).
      rewrite Hother; [ rewrite OLD by (apply ridx_range); apply HRr; exact Hr0 |].
      unfold sl_clob. rewrite (bv_eqb_neq _ _ N11), (bv_eqb_neq _ _ N12), (bv_eqb_neq _ _ N14), (bv_eqb_neq _ _ N15),
        (bv_eqb_neq _ _ N16), (bv_eqb_neq _ _ N19). reflexivity.
    + constructor.
      * cbn [kentry_ok edenot]. rewrite X0, u64_lit by lia. lia.
      * eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
    + intros R' FULL' model' HC' Hfs'. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs'].
      split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Theorem node_bysizelog_sound :
  APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (SLN.node_bysizelog nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold SLN.node_bysizelog in Hn.
  destruct (Z.eqb (pc cs) (SLN.bs_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (split_lit (eaddz (reg cs 9) 96)) as [wb wk] eqn:Hsw. cbv zeta in Hn.
  destruct (xlo (kn cs) (reg cs 11)) as [ilo|] eqn:Hilo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [ihi|] eqn:Hihi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 9)) as [slo|] eqn:Hslo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 9)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hflw]. apply andb_prop in Hcond as [Hcond Hwr].
  apply andb_prop in Hcond as [Hcond Hs64]. apply andb_prop in Hcond as [Hcond Hs0]. apply andb_prop in Hcond as [Hi0 Hi63].
  apply Z.leb_le in Hi0. apply Z.leb_le in Hi63. apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs64.
  injection Hn as <-.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in R9 by (apply bv_eq; reflexivity).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hilo) as Hilo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hihi) as Hihi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hslo) as Hslo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (iw := edenot E (reg cs 11)) in *. set (i := bv_unsigned iw) in *.
  set (sw := edenot E (reg cs 9)) in *. set (sa := bv_unsigned sw) in *.
  unfold two64 in Hs64. pose proof (u64_range sw) as Hsar. fold sa in Hsar. pose proof (u64_range iw) as Hir. fold i in Hir.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ wb wk Hsw) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold sw in Hq. unfold v_add in Hq.
  rewrite (u64_lit 96) in Hq by lia. fold sa in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) wb wk SLN.BS_WIN HKN HKN Hwr ltac:(unfold SLN.BS_WIN; lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA wb wk)) in *.
  assert (HQ : Q = sa + 96).
  { change (bv_unsigned (edenot E wb) + wk) with Q in Hq. apply (f_equal bv_unsigned) in Hq. rewrite !u64_lit in Hq by (unfold SLN.BS_WIN in *; lia). lia. }
  assert (Hstk : forall a, sa + 96 <= a < sa + 616 -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M (Z.to_nat SLN.BS_WIN) (Z_to_bv 64 Q)); [rewrite u64_lit by lia; unfold SLN.BS_WIN; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. unfold SLN.BS_WIN. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  destruct (BSSPEC M R i sa ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(rewrite R11; fold iw; symmetry; apply Z_to_bv_bv_unsigned)
              ltac:(rewrite R9; fold sw; symmetry; apply Z_to_bv_bv_unsigned) Hstk)
    as (regs' & M' & Hms & Hother & Hout & Hgr).
  set (VALS := [getr regs' 11%bv; getr regs' 13%bv]).
  set (E' := ext_list E (nxt cs) VALS).
  pose proof (ext_list_agree E (nxt cs) VALS) as Hag. fold E' in Hag.
  pose proof (ext_list_at E (nxt cs) VALS 0 ltac:(cbn; lia)) as X0. fold E' in X0. cbn [nth VALS] in X0.
  pose proof (ext_list_at E (nxt cs) VALS 1 ltac:(cbn; lia)) as X1. fold E' in X1. cbn [nth VALS] in X1.
  replace (nxt cs + 0)%nat with (nxt cs) in X0 by lia. replace (nxt cs + 1)%nat with (S (nxt cs)) in X1 by lia.
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
            cs E E' R FULL model TT (SLN.bs_exit T) (sr_upd (sr_upd (s_regs (a_ss cs)) 11 (EVar (nxt cs))) 13 (EVar (S (nxt cs))))
            (kn_havoc (kn cs) wb wk (ELit SLN.BS_WIN)) (S (S (nxt cs))) regs' M' HC Hfresh Hag).
  - rewrite Hpc. exact Hms.
  - apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    assert (OLD : forall j, (j < 32)%nat -> edenot E' (nth j (s_regs (a_ss cs)) (ELit 0)) = edenot E (nth j (s_regs (a_ss cs)) (ELit 0))).
    { intros j Hj. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
    assert (RX : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> Nat.eqb (ridx r) n = true -> r = rr).
    { intros n rr Hn' Hrb EQ1. apply Nat.eqb_eq in EQ1. rewrite (reg_of_ridx r n EQ1). apply bv_eq.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrb. }
    rewrite !nth_sr_upd.
    destruct (Nat.eqb (ridx r) 13) eqn:E13; [apply (RX 13%nat 13%bv ltac:(lia) eq_refl) in E13; subst r; cbn [edenot]; symmetry; exact X1|].
    destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (RX 11%nat 11%bv ltac:(lia) eq_refl) in E11; subst r; cbn [edenot]; symmetry; exact X0|].
    assert (N11 : r <> 11%bv) by (intros ->; cbv in E11; discriminate E11).
    assert (N13 : r <> 13%bv) by (intros ->; cbv in E13; discriminate E13).
    rewrite Hother; [ rewrite OLD by (apply ridx_range); apply HRr; exact Hr0 |].
    unfold bs_clob. rewrite (bv_eqb_neq _ _ N11), (bv_eqb_neq _ _ N13). reflexivity.
  - eapply know_ok_agree'; [exact Hag | exact Hkv | ].
    eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
      intros x Hx. change (estart E (SA wb wk)) with Q in Hx.
      replace (elenZ E (ELit SLN.BS_WIN)) with 520 in Hx by (unfold elenZ, SLN.BS_WIN; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
      apply Hout. lia.
  - intros R' FULL' model' HC' Hfs'. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs'].
    split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Theorem sl_xn_sound : forall id args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (SLN.xn SEGS nx0 T id args).
Proof.
  intros id args. unfold SLN.xn.
  destruct (Nat.eqb id 105); [apply node_sizelog_sound|].
  destruct (Nat.eqb id 106); [apply node_bysizelog_sound|].
  intros cs cs' E R FULL model TT HC _ Hn Hk. discriminate Hn.
Qed.
End Sound.
End WithFP1.

