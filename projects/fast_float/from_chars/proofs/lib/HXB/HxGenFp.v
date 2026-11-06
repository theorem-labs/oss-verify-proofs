(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.

Module HxLoopR.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition bare_reg (k : Z) (s : sst) : sst :=
  let l := rget (s_regs s) (rkz k) in let w := swin (s_facts s) l in
  if (Z.leb 0 (fst w) && Z.ltb (snd w) two64)%bool
  then SST (s_pc s) (s_regs s) (s_rgs s) (FRange l (fst w) (snd w) :: s_facts s) (s_next s) (s_resv s) else s.
Definition bare_regs (ks : list Z) (s : sst) : sst := List.fold_left (fun s k => bare_reg k s) ks s.

Lemma bare_reg_same : forall k s, s_pc (bare_reg k s) = s_pc s /\ s_rgs (bare_reg k s) = s_rgs s /\ s_next (bare_reg k s) = s_next s.
Proof. intros k s. unfold bare_reg. destruct (Z.leb 0 _ && Z.ltb _ two64)%bool; cbn; repeat split; reflexivity. Qed.
Lemma bare_regs_same : forall ks s, s_pc (bare_regs ks s) = s_pc s /\ s_rgs (bare_regs ks s) = s_rgs s /\ s_next (bare_regs ks s) = s_next s.
Proof.
  intros ks. induction ks as [|k ks IH]; intros s; [repeat split; reflexivity|]. cbn [bare_regs fold_left]. fold (bare_regs ks (bare_reg k s)).
  destruct (IH (bare_reg k s)) as (A & B & C). destruct (bare_reg_same k s) as (A' & B' & C'). rewrite A, B, C. repeat split; assumption.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma bare_reg_sden : forall k E s ms, sden segs E s ms -> sden segs E (bare_reg k s) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k E s ms Hd. unfold bare_reg. set (l := rget (s_regs s) (rkz k)). set (w := swin (s_facts s) l).
  destruct (Z.leb 0 (fst w) && Z.ltb (snd w) two64)%bool eqn:Hc; [|exact Hd].
  apply andb_prop in Hc as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  intros E' Ha. cbn [s_next] in Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
  constructor; [|exact HF0]. cbn [fact_ok].
  destruct (swin_sound E' (s_facts s) l HF0) as (v & Hv & Hr). fold w in Hr.
  pose proof (u_range E' l) as Hu. unfold eqm in Hv. rewrite (Z.mod_small (bv_unsigned (lden E' l))) in Hv by exact Hu.
  rewrite Z.mod_small in Hv by lia. lia.
Qed.
#[using="Type"] Lemma bare_regs_sden : forall ks E s ms, sden segs E s ms -> sden segs E (bare_regs ks s) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ks. induction ks as [|k ks IH]; intros E s ms Hd; [exact Hd|]. cbn [bare_regs fold_left]. fold (bare_regs ks (bare_reg k s)).
  apply IH, bare_reg_sden, Hd.
Qed.

(* [comment removed for export] *)
Definition hook_ok (t : tree xi) (h : sst -> option sst) : Prop :=
  forall s s' E ms, h s = Some s' -> sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists ms' E', isteps segs ms ms' /\ sden segs E' s' ms' /\ agree (s_next s) E E' /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs s') = shape (s_rgs s) /\
    (s_next s <= s_next s')%positive /\ rtm (s_rgs s') = rtm (s_rgs s) /\ fpc t ms ms'.

Definition hook_bare (ks : list Z) (s : sst) : option sst := Some (bare_regs ks s).
#[using="Type"] Lemma hook_bare_ok : forall t ks, hook_ok t (hook_bare ks).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t ks s s' E ms H Hd _. injection H as <-. destruct (bare_regs_same ks s) as (_ & Hrg & Hnx).
  exists ms, E. split; [constructor|]. split; [exact (bare_regs_sden ks E s ms Hd)|]. split; [apply agree_refl|].
  split; [intros; reflexivity|]. rewrite Hrg, Hnx. split; [reflexivity|]. split; [lia|]. split; [reflexivity | apply fpc_refl].
Qed.

(* [comment removed for export] *)
Definition is_sra (op : aluop) : bool := match op with ALU_SRA => true | _ => false end.
Definition hook_sra63 (t : tree xi) (s : sst) : option sst :=
  match tlookup t (s_pc s) with
  | XAluI op rd rs imm =>
      if (is_sra op && Z.eqb imm 63 && Z.ltb (snd (irange (s_facts s) (rget (s_regs s) rs))) 9223372036854775808)%bool
      then Some (set_res s rd (Some (lconst 0)) FxCore.nofacts (s_pc s + 4)) else None
  | _ => None
  end.

#[using="Type"] Lemma sra63_zero : forall (v b : word), bv_unsigned v < 9223372036854775808 -> bv_unsigned b = 63 -> alu64 ALU_SRA v b = Z_to_bv 64 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros v b Hv Hb. apply bv_eq.
  change (alu64 ALU_SRA v b) with (bv_ashiftr v (bv_and b (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, (signed_small v Hv), bv_and_unsigned, Hb.
  change (bv_unsigned (Z_to_bv 64 63)) with 63. change (Z.land 63 63) with 63.
  pose proof (bv_unsigned_in_range _ v) as X. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (change (2 ^ 63) with 9223372036854775808; lia).
  reflexivity.
Qed.

#[using="Type"] Lemma hook_sra63_ok : forall t, tbl_ok segs t -> hook_ok t (hook_sra63 t).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t Ht s s' E ms H Hden _. unfold hook_sra63 in H.
  destruct (tlookup t (s_pc s)) as [op rd rs imm | | | | | | | | | | | | | | | | | | | | | ] eqn:Hx; try discriminate H.
  destruct (is_sra op && Z.eqb imm 63 && Z.ltb (snd (irange (s_facts s) (rget (s_regs s) rs))) 9223372036854775808)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc Hr]. apply andb_prop in Hc as [Hop Him]. apply Z.ltb_lt in Hr. apply Z.eqb_eq in Him. subst imm.
  destruct op; try discriminate Hop. clear Hop.
  pose proof (sden_0 _ _ _ _ Hden) as Hd0. destruct Hd0 as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  pose proof (mks_eta ms Hsvc) as Hms. rewrite Hpc in Hms.
  destruct (Ht (s_pc s) _ Hx ltac:(discriminate) ltac:(discriminate)) as (w & i & Hfetch & Hecall & Hdecode & Hxl).
  assert (Hst0 : RiscvSemantics.step segs ms = RiscvSemantics.step segs (mks (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (Z_to_bv 64 (s_pc s)) (ms_resv ms) (ms_mem ms) (ms_rom ms)))
    by (f_equal; exact Hms).
  assert (Hnof : nofp_xi (tlookup t (s_pc s)) = true) by (rewrite Hx; reflexivity).
  destruct (xl_aluI _ _ _ _ _ _ Hxl) as [(rd' & rs' & im & -> & -> & -> & Him) | (rd' & rs' & im & -> & -> & -> & Him)].
  - assert (Hval : alu64 ALU_SRA (getr (ms_regs ms) rs') (sext 64 im) = Z_to_bv 64 0).
    { apply sra63_zero; [|symmetry; exact Him]. rewrite (HR rs'). pose proof (irange_sound E _ (rget (s_regs s) (rkey rs')) HF) as X. lia. }
    edestruct (res_sound segs E s ms rd' (Some (lconst 0)) FxCore.nofacts (s_pc s + 4) (alu64 ALU_SRA (getr (ms_regs ms) rs') (sext 64 im)) (ms_fregs ms) (ms_fcsr ms))
      as (E' & Ha & Hn & Hs'); [exact Hden | | | exact Hfrm |].
    + intros E' Ha' HR' l Hl. injection Hl as <-. rewrite Hval. apply lden_lconst.
    + intros E'' Ha'' Hv. constructor.
    + eexists _, E'. split; [eapply ist_step; [exact Hsvc | rewrite Hst0; eapply g_opimm; eassumption | apply ist_refl]|].
      split; [rewrite ?pc_plus4; exact Hs'|]. split; [exact Ha|]. split; [intros x Hxo; reflexivity|].
      rewrite ?s_rgs_set_res. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
      intros Hnf. split; [intros r; reflexivity | reflexivity].
  - assert (Hval : alu64 ALU_SRA (getr (ms_regs ms) rs') (zext 64 im) = Z_to_bv 64 0).
    { apply sra63_zero; [|symmetry; exact Him]. rewrite (HR rs'). pose proof (irange_sound E _ (rget (s_regs s) (rkey rs')) HF) as X. lia. }
    edestruct (res_sound segs E s ms rd' (Some (lconst 0)) FxCore.nofacts (s_pc s + 4) (alu64 ALU_SRA (getr (ms_regs ms) rs') (zext 64 im)) (ms_fregs ms) (ms_fcsr ms))
      as (E' & Ha & Hn & Hs'); [exact Hden | | | exact Hfrm |].
    + intros E' Ha' HR' l Hl. injection Hl as <-. rewrite Hval. apply lden_lconst.
    + intros E'' Ha'' Hv. constructor.
    + eexists _, E'. split; [eapply ist_step; [exact Hsvc | rewrite Hst0; eapply g_shiftimm; eassumption | apply ist_refl]|].
      split; [rewrite ?pc_plus4; exact Hs'|]. split; [exact Ha|]. split; [intros x Hxo; reflexivity|].
      rewrite ?s_rgs_set_res. split; [reflexivity|]. split; [exact Hn|]. split; [reflexivity|].
      intros Hnf. split; [intros r; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Fixpoint hook_at (hooks : list (Z * (sst -> option sst))) (pc : Z) : option (sst -> option sst) :=
  match hooks with [] => None | (a, h) :: r => if Z.eqb a pc then Some h else hook_at r pc end.
Fixpoint explore_h (t : tree xi) (img : tree Z) (n : nat) (fuel : nat) (hooks : list (Z * (sst -> option sst))) (stops : list Z) (s : sst) : list sst :=
  match n with
  | O => fx_explore t img fuel stops s []
  | S n' =>
      List.flat_map (fun L => match hook_at hooks (s_pc L) with
                              | Some h => explore_h t img n' fuel hooks stops (match h L with Some L' => L' | None => L end)
                              | None => [L]
                              end)
                    (fx_explore t img fuel (List.map fst hooks ++ stops) s [])
  end.

Definition hooks_ok (t : tree xi) (hooks : list (Z * (sst -> option sst))) : Prop := forall pc h, In (pc, h) hooks -> hook_ok t h.
#[using="Type"] Lemma hook_at_in : forall hooks pc h, hook_at hooks pc = Some h -> exists a, In (a, h) hooks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hooks. induction hooks as [|[a h0] r IH]; intros pc h H; cbn [hook_at] in H; [discriminate|].
  destruct (Z.eqb a pc); [injection H as <-; exists a; left; reflexivity | destruct (IH pc h H) as (b & Hb); exists b; right; exact Hb].
Qed.

#[using="Type"] Lemma explore_h_frp : forall t img hooks, tbl_ok segs t -> img_ok segs img -> hooks_ok t hooks ->
  forall n fuel stops s E ms, sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists L ms' E', In L (explore_h t img n fuel hooks stops s) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\
    (s_next s <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img hooks Ht Himg Hh n. induction n as [|n IH]; intros fuel stops s E ms Hden Hwf; cbn [explore_h].
  - exact (explore_frame2_frp segs t img fuel stops s [] E ms Ht Himg Hden Hwf).
  - destruct (explore_frame2_frp segs t img fuel (List.map fst hooks ++ stops) s [] E ms Ht Himg Hden Hwf)
      as (L1 & ms1 & E1 & HL1 & Hst1 & Hd1 & Ha1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
    assert (Hb1 : bases_wf (s_next L1) (s_rgs L1) = true) by exact (bases_wf_shape _ _ _ _ Hn1 Hsh1 Hwf).
    destruct (hook_at hooks (s_pc L1)) as [h|] eqn:Hat.
    + (* [comment removed for export] *)
      assert (Hmid : exists L1' ms1' E1', (match h L1 with Some L' => L' | None => L1 end) = L1' /\ isteps segs ms1 ms1' /\ sden segs E1' L1' ms1' /\ agree (s_next L1) E1 E1' /\
                 (forall x, fr_pt E1 (s_rgs L1) x -> ms_mem ms1' x = ms_mem ms1 x) /\ shape (s_rgs L1') = shape (s_rgs L1) /\
                 (s_next L1 <= s_next L1')%positive /\ rtm (s_rgs L1') = rtm (s_rgs L1) /\ fpc t ms1 ms1').
      { destruct (h L1) as [L'|] eqn:HhL.
        - destruct (hook_at_in _ _ _ Hat) as (a & Hin). destruct (Hh a h Hin L1 L' E1 ms1 HhL Hd1 Hb1) as (ms1' & E1' & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
          exists L', ms1', E1'. exact (conj eq_refl (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 B8)))))))).
        - exists L1, ms1, E1. split; [reflexivity|]. split; [constructor|]. split; [exact Hd1|]. split; [apply agree_refl|].
          split; [intros; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity | apply fpc_refl]. }
      destruct Hmid as (L1' & ms1' & E1' & HeqL & Hst1' & Hd1' & Ha1' & Hfr1' & Hsh1' & Hn1' & Hrt1' & Hfp1').
      assert (Hb1' : bases_wf (s_next L1') (s_rgs L1') = true) by exact (bases_wf_shape _ _ _ _ Hn1' Hsh1' Hb1).
      destruct (IH fuel stops L1' E1' ms1' Hd1' Hb1') as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
      exists L2, ms2, E2. split.
      { apply in_flat_map. exists L1. split; [exact HL1|]. rewrite Hat, HeqL. exact HL2. }
      split; [eapply isteps_trans; [exact Hst1 | eapply isteps_trans; [exact Hst1' | exact Hst2]]|]. split; [exact Hd2|].
      split; [intros x Hx; rewrite (Ha1 x Hx); rewrite (Ha1' x ltac:(lia)); apply Ha2; lia|].
      split; [|split; [rewrite Hsh2, Hsh1'; exact Hsh1 | split; [lia | split; [rewrite Hrt2, Hrt1'; exact Hrt1 | exact (fpc_trans _ _ _ _ Hfp1 (fpc_trans _ _ _ _ Hfp1' Hfp2))]]]].
      intros x Hx.
      assert (Hx1 : fr_pt E1 (s_rgs L1) x).
      { apply (fr_pt_shape E1 (s_rgs s) (s_rgs L1) x Hsh1 Hrt1). apply (fr_pt_agree (s_next s) E E1 (s_rgs s) x Hwf Ha1). exact Hx. }
      assert (Hx1' : fr_pt E1' (s_rgs L1') x).
      { apply (fr_pt_shape E1' (s_rgs L1) (s_rgs L1') x Hsh1' Hrt1'). apply (fr_pt_agree (s_next L1) E1 E1' (s_rgs L1) x Hb1 Ha1'). exact Hx1. }
      rewrite (Hfr2 x Hx1'), (Hfr1' x Hx1). exact (Hfr1 x Hx).
    + exists L1, ms1, E1. split; [apply in_flat_map; exists L1; split; [exact HL1 | rewrite Hat; left; reflexivity]|].
      split; [exact Hst1|]. split; [exact Hd1|]. split; [exact Ha1|]. split; [exact Hfr1|]. split; [exact Hsh1|]. split; [exact Hn1|]. split; [exact Hrt1 | exact Hfp1].
Qed.

(* [comment removed for export] *)
Definition loop_leaves2 (t : tree xi) (img : tree Z) (ls : loopspec) (hooks : list (Z * (sst -> option sst))) : list sst :=
  explore_h t img (List.length hooks) (ls_fuel ls) hooks (s_pc (ls_inv ls) :: ls_stops ls) (ls_inv ls).

Definition loop_check2 (t : tree xi) (img : tree Z) (ls : loopspec) (hooks : list (Z * (sst -> option sst))) : option (list sst) :=
  let P := ls_inv ls in
  if (state_wf P && lwf (s_next P) (ls_meas ls) && forallb (fun x => Pos.ltb x (s_next P)) (ls_params ls))%bool then
    let leaves := loop_leaves2 t img ls hooks in
    if forallb (fun L => if Z.eqb (s_pc L) (s_pc P) then back_ok P (ls_meas ls) (ls_params ls) L else true) leaves
    then Some (List.filter (fun L => negb (Z.eqb (s_pc L) (s_pc P))) leaves) else None
  else None.

#[using="Type"] Lemma body2_frp : forall t img ls hooks, tbl_ok segs t -> img_ok segs img -> hooks_ok t hooks -> bases_wf (s_next (ls_inv ls)) (s_rgs (ls_inv ls)) = true ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L (loop_leaves2 t img ls hooks) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next (ls_inv ls)) E E' /\
    (forall x, fr_pt E (s_rgs (ls_inv ls)) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs (ls_inv ls)) /\
    (s_next (ls_inv ls) <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs (ls_inv ls)) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0. intros t img ls hooks Ht Himg Hh HbP E ms Hden. exact (explore_h_frp t img hooks Ht Himg Hh _ _ _ _ E ms Hden HbP). Qed.

#[using="Type"] Lemma loop_check2_wf : forall t img ls hooks exits, loop_check2 t img ls hooks = Some exits -> state_wf (ls_inv ls) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls hooks exits H. unfold loop_check2 in H.
  destruct (state_wf (ls_inv ls) && lwf (s_next (ls_inv ls)) (ls_meas ls) && forallb (fun x => Pos.ltb x (s_next (ls_inv ls))) (ls_params ls))%bool eqn:Hw; [|discriminate].
  apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. exact Hw.
Qed.

#[using="Type"] Theorem loop_frame2_frp : forall t img ls hooks exits, tbl_ok segs t -> img_ok segs img -> hooks_ok t hooks -> loop_check2 t img ls hooks = Some exits ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L exits /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\
    (forall x, fr_pt E (s_rgs (ls_inv ls)) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs (ls_inv ls)) /\
    (s_next (ls_inv ls) <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs (ls_inv ls)) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls hooks exits Ht Himg Hh Hck. unfold loop_check2 in Hck.
  set (P := ls_inv ls) in *. set (m := ls_meas ls) in *.
  destruct (state_wf P && lwf (s_next P) m && forallb (fun x => Pos.ltb x (s_next P)) (ls_params ls))%bool eqn:Hw; [|discriminate].
  apply andb_prop in Hw as [Hw Hps]. apply andb_prop in Hw as [HwP Hwm]. rewrite forallb_forall in Hps.
  pose proof (state_wf_bases P HwP) as HbP.
  destruct (forallb (fun L => if Z.eqb (s_pc L) (s_pc P) then back_ok P m (ls_params ls) L else true) (loop_leaves2 t img ls hooks)) eqn:Hall;
    [|discriminate].
  injection Hck as <-. rewrite forallb_forall in Hall.
  assert (Hind : forall n, forall E ms, Z.to_nat (bv_unsigned (lden E m)) = n -> sden segs E P ms ->
            exists L ms' E', In L (List.filter (fun L => negb (Z.eqb (s_pc L) (s_pc P))) (loop_leaves2 t img ls hooks)) /\
                             isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\
                             (forall x, fr_pt E (s_rgs P) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs P) /\
                             (s_next P <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs P) /\ fpc t ms ms').
  { intros n. induction n as [n IH] using (well_founded_induction lt_wf). intros E ms Hn Hden.
    destruct (body2_frp t img ls hooks Ht Himg Hh HbP E ms Hden) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
    fold P in HL, Ha1, Hfr1, Hsh1, Hn1, Hrt1.
    assert (Hpar : forall x, In x (ls_params ls) -> E1 x = E x) by (intros x Hx; symmetry; apply Ha1; apply Pos.ltb_lt, Hps, Hx).
    pose proof (Hall L HL) as HLok.
    destruct (Z.eqb (s_pc L) (s_pc P)) eqn:Hpc.
    - unfold back_ok in HLok. set (σ := match_st L P) in HLok.
      apply andb_prop in HLok as [HLok Hdec]. apply andb_prop in HLok as [Hent Hfix].
      pose proof (sden_0 _ _ _ _ Hd1) as Hd10.
      pose proof (entails_sden segs E1 L P σ ms1 Hd10 Hent HwP) as HdP.
      destruct Hd10 as (_ & _ & _ & _ & _ & _ & HF1 & _).
      pose proof (meas_dec_sound E1 L σ m HF1 Hdec) as Hlt. rewrite lden_lsubst in Hlt.
      rewrite (lden_agree (s_next P) E1 E m Hwm (fun x Hx => eq_sym (Ha1 x Hx))) in Hlt.
      destruct (IH (Z.to_nat (bv_unsigned (lden (ecomp E1 σ) m))) ltac:(pose proof (u_range (ecomp E1 σ) m); lia) (ecomp E1 σ) ms1 eq_refl HdP)
        as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hpar2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
      exists L2, ms2, E2. split; [exact HL2|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
      split; [intros x Hx; rewrite (Hpar2 x Hx); rewrite (params_fixed_sound E1 σ _ x Hfix Hx); apply Hpar; exact Hx|].
      split; [|split; [exact Hsh2 | split; [exact Hn2 | split; [exact Hrt2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]]].
      intros x Hx. rewrite Hfr2; [exact (Hfr1 x Hx)|].
      unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hrg].
      apply (fr_pt_ent E1 (s_rgs L) (s_rgs P) σ x Hrg).
      apply (fr_pt_shape E1 (s_rgs P) (s_rgs L) x Hsh1 Hrt1).
      apply (fr_pt_agree (s_next P) E E1 (s_rgs P) x HbP Ha1). exact Hx.
    - exists L, ms1, E1. split; [apply (proj2 (filter_In _ _ _)); split; [exact HL | rewrite Hpc; reflexivity]|].
      split; [exact Hst1|]. split; [exact Hd1|]. split; [exact Hpar|]. split; [exact Hfr1 | split; [exact Hsh1 | split; [exact Hn1 | split; [exact Hrt1 | exact Hfp1]]]]. }
  intros E ms Hden. exact (Hind _ E ms eq_refl Hden).
Qed.
End WithSegs.

(* [comment removed for export] *)
Definition hx_loopr (t : tree xi) (img : tree Z) (gen : sst -> option loopspec) (hooks : list (Z * (sst -> option sst))) (X : xst) : option (list xst) :=
  let s := xs_st X in
  match gen s with
  | Some ls =>
      let σ := match_st s (ls_inv ls) in
      let ins := vars_below (s_next s) in
      if (entails s (ls_inv ls) σ && params_fixed σ ins && forallb (fun x => existsb (Pos.eqb x) (ls_params ls)) ins
          && shape_eqb (s_rgs s) (s_rgs (ls_inv ls)) && Pos.leb (s_next s) (s_next (ls_inv ls)))%bool then
        match loop_check2 t img ls hooks with
        | Some exits => Some (List.map (fun L => XST L (xs_x X)) exits)
        | None => None
        end
      else None
  | None => None
  end.

Section HxLoopRSound.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

#[using="Type"] Theorem hx_loopr_okP : forall (Φ : machine_state -> machine_state -> Prop) t img gen hooks, tbl_ok segs t -> img_ok segs img ->
  (forall a b, fpc t a b -> Φ a b) -> hooks_ok segs t hooks -> hand_okxP segs xok Φ (hx_loopr t img gen hooks).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ t img gen hooks Ht Himg HΦ Hh X Ks E ms m0 Hf Hd HxF Hxw Hm0. unfold hx_loopr in Hf. set (s := xs_st X) in *.
  destruct (gen s) as [ls|]; [|discriminate]. set (σ := match_st s (ls_inv ls)) in *. set (ins := vars_below (s_next s)) in *.
  destruct (entails s (ls_inv ls) σ && params_fixed σ ins && forallb (fun x => existsb (Pos.eqb x) (ls_params ls)) ins
            && shape_eqb (s_rgs s) (s_rgs (ls_inv ls)) && Pos.leb (s_next s) (s_next (ls_inv ls)))%bool eqn:He; [|discriminate].
  apply andb_prop in He as [He HnP]. apply Pos.leb_le in HnP. apply andb_prop in He as [He Hsheq]. apply andb_prop in He as [He Hpar].
  apply andb_prop in He as [Hent Hfix]. pose proof (shape_eqb_eq _ _ Hsheq) as HshP.
  destruct (loop_check2 t img ls hooks) as [exits|] eqn:Hlc; [|discriminate]. injection Hf as <-.
  pose proof (loop_check2_wf _ _ _ _ _ Hlc) as HwP.
  pose proof (entails_sden segs E s (ls_inv ls) σ ms (sden_0 _ _ _ _ Hd) Hent HwP) as HdP.
  destruct (loop_frame2_frp segs t img ls hooks exits Ht Himg Hh Hlc (ecomp E σ) ms HdP) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Hp1 & Hfr1 & Hsh1 & Hn1 & Hrt1 & Hfp1).
  assert (Hag : agree (s_next s) E E1).
  { intros x Hx. assert (Hin : In x ins) by (apply in_vars_below; exact Hx).
    rewrite forallb_forall in Hpar. pose proof (Hpar x Hin) as Hxp. apply existsb_exists in Hxp as (z & Hz & Hxz). apply Pos.eqb_eq in Hxz. subst z.
    rewrite (Hp1 x Hz). symmetry. apply (params_fixed_sound E σ ins x Hfix Hin). }
  assert (Hrg : rgs_ent (s_rgs s) (s_rgs (ls_inv ls)) σ = true).
  { unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hrg]. exact Hrg. }
  exists (XST L (xs_x X)), ms1, E1. cbn [xs_st xs_x]. split; [exact (in_map (fun L => XST L (xs_x X)) exits L HL)|]. split; [exact Hst1|]. split; [exact Hd1|]. split; [exact Hag|].
  split; [intros x Hx; apply Hfr1; exact (proj1 (fr_pt_ent E (s_rgs s) (s_rgs (ls_inv ls)) σ x Hrg) Hx)|].
  split; [rewrite Hsh1; symmetry; exact HshP|]. split; [fold s; lia|]. split; [rewrite Hrt1; symmetry; exact (rgs_ent_rtm _ _ _ Hrg)|].
  split; [rewrite Forall_forall in *; intros f0 Hf0; rewrite forallb_forall in Hxw; exact (xfact_ok_agree xok _ E E1 _ f0 (Hxw f0 Hf0) Hag (HxF f0 Hf0))|].
  split; [apply (xwf_mono (s_next s)); [fold s; lia | exact Hxw] | exact (HΦ _ _ Hfp1)].
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem hx_loopr_ok_fp : forall t img gen hooks, tbl_ok segs t -> img_ok segs img -> tbl_nofp t = true -> hooks_ok segs t hooks ->
  hand_okx_fp segs xok (hx_loopr t img gen hooks).
Proof. LiaFast.lf_pins LiaFast.u0. intros t img gen hooks Ht Himg Hnf Hh. apply hx_loopr_okP; [exact Ht | exact Himg | intros a b H; exact (H Hnf) | exact Hh]. Qed.
#[using="Type"] Theorem hx_loopr_ok : forall t img gen hooks, tbl_ok segs t -> img_ok segs img -> hooks_ok segs t hooks -> hand_okx segs xok (hx_loopr t img gen hooks).
Proof. LiaFast.lf_pins LiaFast.u0. intros t img gen hooks Ht Himg Hh. apply (hand_okxP_ok segs xok (fun _ _ => True)). apply hx_loopr_okP; [exact Ht | exact Himg | intros; exact I | exact Hh]. Qed.
End HxLoopRSound.
End HxLoopR.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HxGenFp.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

Definition hx_kit_fp (pc0 pc1 : Z) (keys : list Z) (chk : sst -> bool) (newf : sst -> list fact) (newx : sst -> list xfact) : Prop :=
  forall L XL E ms (m0 : word -> option byte), s_pc L = pc0 -> chk L = true -> state_wf L = true -> sden segs E L ms ->
    Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) ->
    exists ms' vs, isteps segs ms ms' /\ length vs = length keys /\
      ms_mem ms' = ms_mem ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_resv ms' = ms_resv ms /\ ms_svc_pending ms' = None /\
      ms_pc_val ms' = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) keys -> getr (ms_regs ms') r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error keys i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms') (Z_to_bv 5 k) = v) /\
      Forall (fact_ok (E_of keys vs (s_next L) E)) (newf L) /\ Forall (xfact_ok xok (E_of keys vs (s_next L) E) m0) (newx L) /\
      (forall r, reg_get (ms_fregs ms') r = reg_get (ms_fregs ms) r).

#[using="Type"] Theorem hx_ok_fp : forall pc0 pc1 keys chk newf newx, hx_kit_fp pc0 pc1 keys chk newf newx -> hand_okx_fp segs xok (hx_reg pc0 pc1 keys chk newf newx).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc0 pc1 keys chk newf newx HK X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. cbn [xs_st xs_x] in *.
  unfold hx_reg, hx_cont in Hf. cbn [xs_st xs_x] in Hf.
  set (K := SST pc1 (set_fresh (s_regs L) keys (s_next L)) (s_rgs L) (newf L ++ s_facts L) (Pos.of_nat (Pos.to_nat (s_next L) + length keys))
                (s_resv L)) in *.
  destruct (Z.eqb (s_pc L) pc0 && chk L && keys_ok keys && state_wf L && state_wf K
            && forallb (xwf (s_next K)) (newx L))%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc HxwN]. apply andb_prop in Hc as [Hc HwK]. apply andb_prop in Hc as [Hc HwL].
  apply andb_prop in Hc as [Hc Hko]. apply andb_prop in Hc as [Hpc Hchk]. apply Z.eqb_eq in Hpc.
  destruct (HK L XL E ms m0 Hpc Hchk HwL Hd HxF Hm0)
    as (ms' & vs & Hst & Hlen & Hmem & Hfc & Hrv & Hsvc & Hpc' & Hnk & Hkv & HnF & HnX & Hfr).
  set (E' := E_of keys vs (s_next L) E).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  assert (HnK : (s_next L <= Pos.of_nat (Pos.to_nat (s_next L) + length keys))%positive).
  { apply Pos2Nat.inj_le. rewrite Nat2Pos.id by lia. lia. }
  exists (XST K (newx L ++ XL)), ms', E'. split; [left; reflexivity|]. split; [exact Hst|].
  cbn [xs_st xs_x].
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold state_wf in HwL. apply andb_prop in HwL as [HwL Hwv]. apply andb_prop in HwL as [HwL Hwf]. apply andb_prop in HwL as [Hwr Hwg].
  split; [|split; [exact Hag|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply sden0_sden; [exact HwK|]. unfold sden0. unfold K. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc'|]. split; [exact Hsvc|].
    split.
    { rewrite Hrv. revert Hresv0 Hwv. destruct (s_resv L) as [|l|]; cbn [rsv_ok rsv_wf]; intros Hresv1 Hwv1.
      - exact Hresv1.
      - rewrite <- (lden_agree _ E E' l Hwv1 Hag). exact Hresv1.
      - exact I. }
    split; [|split; [|split; [|split]]].
    + intros r. apply (set_fresh_ok keys vs (s_next L) E (s_regs L) (getr (ms_regs ms)) (getr (ms_regs ms'))); try assumption.
      intros r0. destruct (decide (r0 = 0%bv)) as [->|Hr0]; [change (rkey 0%bv) with xH; reflexivity|].
      destruct (rkey_succ r0 Hr0) as (k & Hk & Ek). rewrite Ek. exact (regs_wf_n_spec _ _ 31 Hwr k Hk).
    + rewrite Hmem. apply Forall_forall. intros R HR. rewrite forallb_forall in Hwg. rewrite Forall_forall in HG0.
      exact (rg_ok_agree segs _ E E' _ R (Hwg R HR) Hag (HG0 R HR)).
    + exact (rgs_disj_agree _ E E' _ Hwg Hag HD0).
    + apply Forall_app. split; [exact HnF|]. apply Forall_forall. intros f Hf. rewrite forallb_forall in Hwf. rewrite Forall_forall in HF0.
      exact (fact_ok_agree _ E E' f (Hwf f Hf) Hag (HF0 f Hf)).
    + rewrite Hfc. exact Hfrm0.
  - intros x Hx. rewrite Hmem. reflexivity.
  - reflexivity.
  - exact HnK.
  - reflexivity.
  - apply Forall_app. split; [exact HnX|]. rewrite Forall_forall in *. intros f Hf. rewrite forallb_forall in Hxw.
    exact (xfact_ok_agree xok _ E E' m0 f (Hxw f Hf) Hag (HxF f Hf)).
  - rewrite forallb_app. rewrite HxwN. cbn [andb]. apply (xwf_mono (s_next L)); [exact HnK | exact Hxw].
  - split; [exact Hfr | exact Hfc].
Qed.

Definition hx_kitm_fp (pc0 : Z) (keys : list Z) (chk : xst -> bool) (exits : list hx_exit) : Prop :=
  forall L XL E ms (m0 : word -> option byte), s_pc L = pc0 -> chk (XST L XL) = true -> state_wf L = true -> sden segs E L ms ->
    Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) ->
    exists pc1 newf newx ms' vs, In (pc1, newf, newx) exits /\ isteps segs ms ms' /\ length vs = length keys /\
      ms_mem ms' = ms_mem ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_resv ms' = ms_resv ms /\ ms_svc_pending ms' = None /\
      ms_pc_val ms' = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) keys -> getr (ms_regs ms') r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error keys i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms') (Z_to_bv 5 k) = v) /\
      Forall (fact_ok (E_of keys vs (s_next L) E)) (newf L) /\ Forall (xfact_ok xok (E_of keys vs (s_next L) E) m0) (newx L) /\
      (forall r, reg_get (ms_fregs ms') r = reg_get (ms_fregs ms) r).

#[using="Type"] Theorem hx_okm_fp : forall pc0 keys chk exits, hx_kitm_fp pc0 keys chk exits -> hand_okx_fp segs xok (hx_regm pc0 keys chk exits).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc0 keys chk exits HK X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. cbn [xs_st xs_x] in *.
  unfold hx_regm in Hf. cbn [xs_st xs_x] in Hf.
  destruct (Z.eqb (s_pc L) pc0 && chk (XST L XL) && keys_ok keys && state_wf L
            && forallb (fun '(pc1, newf, newx) =>
                    let K := hx_cont pc1 keys newf newx (XST L XL) in
                    (state_wf (xs_st K) && forallb (xwf (s_next (xs_st K))) (newx L))%bool) exits)%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hall]. apply andb_prop in Hc as [Hc HwL].
  apply andb_prop in Hc as [Hc Hko]. apply andb_prop in Hc as [Hpc Hchk]. apply Z.eqb_eq in Hpc.
  destruct (HK L XL E ms m0 Hpc Hchk HwL Hd HxF Hm0)
    as (pc1 & newf & newx & ms' & vs & Hin & Hst & Hlen & Hmem & Hfc & Hrv & Hsvc & Hpc' & Hnk & Hkv & HnF & HnX & Hfr).
  rewrite forallb_forall in Hall. pose proof (Hall _ Hin) as Hex. cbn beta iota in Hex. apply andb_prop in Hex as [HwK HxwN].
  set (K := SST pc1 (set_fresh (s_regs L) keys (s_next L)) (s_rgs L) (newf L ++ s_facts L) (Pos.of_nat (Pos.to_nat (s_next L) + length keys))
                (s_resv L)) in *.
  set (E' := E_of keys vs (s_next L) E).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  assert (HnK : (s_next L <= Pos.of_nat (Pos.to_nat (s_next L) + length keys))%positive).
  { apply Pos2Nat.inj_le. rewrite Nat2Pos.id by lia. lia. }
  exists (XST K (newx L ++ XL)), ms', E'.
  split; [unfold hx_conts; apply in_map_iff; exists (pc1, newf, newx); split; [reflexivity | exact Hin]|]. split; [exact Hst|].
  cbn [xs_st xs_x].
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold state_wf in HwL. apply andb_prop in HwL as [HwL Hwv]. apply andb_prop in HwL as [HwL Hwf]. apply andb_prop in HwL as [Hwr Hwg].
  split; [|split; [exact Hag|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply sden0_sden; [exact HwK|]. unfold sden0. unfold K. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc'|]. split; [exact Hsvc|].
    split.
    { rewrite Hrv. revert Hresv0 Hwv. destruct (s_resv L) as [|l|]; cbn [rsv_ok rsv_wf]; intros Hresv1 Hwv1.
      - exact Hresv1.
      - rewrite <- (lden_agree _ E E' l Hwv1 Hag). exact Hresv1.
      - exact I. }
    split; [|split; [|split; [|split]]].
    + intros r. apply (set_fresh_ok keys vs (s_next L) E (s_regs L) (getr (ms_regs ms)) (getr (ms_regs ms'))); try assumption.
      intros r0. destruct (decide (r0 = 0%bv)) as [->|Hr0]; [change (rkey 0%bv) with xH; reflexivity|].
      destruct (rkey_succ r0 Hr0) as (k & Hk & Ek). rewrite Ek. exact (regs_wf_n_spec _ _ 31 Hwr k Hk).
    + rewrite Hmem. apply Forall_forall. intros R HR. rewrite forallb_forall in Hwg. rewrite Forall_forall in HG0.
      exact (rg_ok_agree segs _ E E' _ R (Hwg R HR) Hag (HG0 R HR)).
    + exact (rgs_disj_agree _ E E' _ Hwg Hag HD0).
    + apply Forall_app. split; [exact HnF|]. apply Forall_forall. intros f Hf. rewrite forallb_forall in Hwf. rewrite Forall_forall in HF0.
      exact (fact_ok_agree _ E E' f (Hwf f Hf) Hag (HF0 f Hf)).
    + rewrite Hfc. exact Hfrm0.
  - intros x Hx. rewrite Hmem. reflexivity.
  - reflexivity.
  - exact HnK.
  - reflexivity.
  - apply Forall_app. split; [exact HnX|]. rewrite Forall_forall in *. intros f Hf. rewrite forallb_forall in Hxw.
    exact (xfact_ok_agree xok _ E E' m0 f (Hxw f Hf) Hag (HxF f Hf)).
  - rewrite forallb_app. apply andb_true_intro. split; [exact HxwN | apply (xwf_mono (s_next L)); [exact HnK | exact Hxw]].
  - split; [exact Hfr | exact Hfc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem hx_rule_ok_fp : forall pc chk newx,
  (forall L XL E ms (m0 : word -> option byte), s_pc L = pc -> chk (XST L XL) = true -> state_wf L = true -> sden segs E L ms ->
     Forall (xfact_ok xok E m0) XL -> (forall x, fr_pt E (s_rgs L) x -> ms_mem ms x = m0 x) -> Forall (xfact_ok xok E m0) (newx L)) ->
  hand_okx_fp segs xok (hx_rule pc chk newx).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc chk newx HR. apply hx_okm_fp. intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & _).
  exists pc, nofacts, newx, ms, []. split; [left; reflexivity|]. split; [apply ist_refl|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsvc0|]. split; [rewrite Hpc0, Hpc; reflexivity|].
  split; [intros; reflexivity|]. split; [intros i k v Hi; destruct i; discriminate|]. split; [constructor|].
  split; [cbn [E_of]; exact (HR L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0) | intros r; reflexivity].
Qed.

#[using="Type"] Theorem hx_fold_ok_fp : forall pc k, hand_okx_fp segs xok (hx_fold pc k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc k X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_fold in Hf. cbn [xs_st xs_x] in *.
  destruct (Z.eqb (s_pc L) pc && Z.eqb (fst (irange (s_facts L) (rget (s_regs L) (rkz k)))) (snd (irange (s_facts L) (rget (s_regs L) (rkz k))))
            && Z.leb 1 k && Z.leb k 31)%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [Hc Hk1]. apply andb_prop in Hc as [_ Heq].
  apply Z.eqb_eq in Heq. apply Z.leb_le in Hk1, Hk2.
  set (l := rget (s_regs L) (rkz k)) in *. set (c := fst (irange (s_facts L) l)) in *.
  eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
  cbn [xs_st xs_x s_pc s_regs s_rgs s_facts s_next s_resv].
  split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [lia|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply fpeq_refl]]]]]]]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj HF0 Hfrm0))))))).
  unfold regs_ok. intros r. destruct (Pos.eq_dec (rkey r) (rkz k)) as [Hq|Hq].
  - rewrite Hq. rewrite rget_rset_same by (apply rkz_ne1; lia). rewrite lden_lconst. rewrite (HR0 r), Hq. fold l.
    pose proof (irange_sound E' (s_facts L) l HF0) as X. fold c in X. rewrite <- Heq in X. fold c in X.
    apply bv_eq. rewrite u_Z_to_bv. pose proof (bv_unsigned_in_range _ (lden E' l)) as B. unfold bv_modulus in B.
    change (2 ^ Z.of_N 64) with two64 in B. rewrite Z.mod_small by lia. lia.
  - rewrite rget_rset_other by exact Hq. exact (HR0 r).
Qed.

(* [comment removed for export] *)
Definition hx_eqreg (pc k j : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  let lk := rget (s_regs L) (rkz k) in let lj := rget (s_regs L) (rkz j) in
  if (Z.eqb (s_pc L) pc && Z.leb 1 k && Z.leb k 31 && fact_implied (s_facts L) (FRange (lsub lk lj) 0 0))%bool
  then Some [XST (SST (s_pc L) (rset (s_regs L) (rkz k) lj) (s_rgs L) (s_facts L) (s_next L) (s_resv L)) (xs_x X)]
  else None.
#[using="Type"] Theorem hx_eqreg_ok_fp : forall pc k j, hand_okx_fp segs xok (hx_eqreg pc k j).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc k j X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_eqreg in Hf. cbn [xs_st xs_x] in *.
  destruct (Z.eqb (s_pc L) pc && Z.leb 1 k && Z.leb k 31
            && fact_implied (s_facts L) (FRange (lsub (rget (s_regs L) (rkz k)) (rget (s_regs L) (rkz j))) 0 0))%bool eqn:Hc; [|discriminate].
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Himp]. apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [_ Hk1].
  apply Z.leb_le in Hk1, Hk2.
  set (lk := rget (s_regs L) (rkz k)) in *. set (lj := rget (s_regs L) (rkz j)) in *.
  eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
  cbn [xs_st xs_x s_pc s_regs s_rgs s_facts s_next s_resv].
  split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [lia|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply fpeq_refl]]]]]]]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj HF0 Hfrm0))))))).
  unfold regs_ok. intros r. destruct (Pos.eq_dec (rkey r) (rkz k)) as [Hq|Hq].
  - rewrite Hq. rewrite rget_rset_same by (apply rkz_ne1; lia). rewrite (HR0 r), Hq. fold lk.
    pose proof (fact_implied_ok E' _ _ HF0 Himp) as X. cbn [fact_ok] in X. rewrite lden_lsub, bv_sub_unsigned in X.
    unfold bv_wrap, bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X.
    pose proof (bv_unsigned_in_range _ (lden E' lk)) as B1. pose proof (bv_unsigned_in_range _ (lden E' lj)) as B2.
    unfold bv_modulus in B1, B2. change (2 ^ Z.of_N 64) with two64 in B1, B2.
    apply bv_eq. unfold two64 in *. Z.div_mod_to_equations. lia.
  - rewrite rget_rset_other by exact Hq. exact (HR0 r).
Qed.
(* [comment removed for export] *)
Definition hx_ssplit (pc k : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  let l := rget (s_regs L) (rkz k) in
  let w := swin (s_facts L) l in
  if (Z.eqb (s_pc L) pc && Z.ltb (fst w) 0 && Z.leb 0 (snd w) && Z.ltb (snd w - fst w) two64)%bool then
    Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (- 1 - fst w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X);
          XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange l 0 (snd w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X)]
  else if Z.eqb (s_pc L) pc then Some [X] else None.
#[using="Type"] Theorem hx_ssplit_ok_fp : forall pc k, hand_okx_fp segs xok (hx_ssplit pc k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc k X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_ssplit in Hf. cbn [xs_st xs_x] in *.
  set (l := rget (s_regs L) (rkz k)) in *. set (w := swin (s_facts L) l) in *.
  destruct (Z.eqb (s_pc L) pc && Z.ltb (fst w) 0 && Z.leb 0 (snd w) && Z.ltb (snd w - fst w) two64)%bool eqn:Hc.
  2: { destruct (Z.eqb (s_pc L) pc); [|discriminate]. injection Hf as <-.
       exists (XST L XL), ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
       split; [exact Hd|]. split; [intros x Hx; reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|].
       split; [apply Pos.le_refl|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact Hxw | apply fpeq_refl]. }
  injection Hf as <-.
  apply andb_prop in Hc as [Hc Hw3]. apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [_ Hw1].
  apply Z.ltb_lt in Hw1, Hw3. apply Z.leb_le in Hw2.
  pose proof (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _ & _ & HF & _).
  destruct (swin_sound E (s_facts L) l HF) as (v & Hv & Hr). fold w in Hr.
  pose proof (u_range E l) as Ul.
  assert (Hcase : {v < 0} + {0 <= v}) by (destruct (Z_lt_ge_dec v 0); [left | right]; lia).
  set (K1 := XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (- 1 - fst w) :: s_facts L) (s_next L) (s_resv L)) XL).
  set (K2 := XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange l 0 (snd w) :: s_facts L) (s_next L) (s_resv L)) XL).
  assert (GEN : forall f, (forall E', lden E' l = lden E l -> fact_ok E' f) ->
                  sden segs E (SST (s_pc L) (s_regs L) (s_rgs L) (f :: s_facts L) (s_next L) (s_resv L)) ms).
  { intros f Hfo E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
    refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
    constructor; [|exact HF0]. apply Hfo.
    pose proof (HR0 (Z_to_bv 5 k)) as X1. pose proof (HR (Z_to_bv 5 k)) as X2. unfold l, rkz. rewrite <- X1, <- X2. reflexivity. }
  destruct Hcase as [Hneg|Hnn].
  - exists K1, ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
    split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [unfold K1; cbn [xs_st s_next]; apply Pos.le_refl|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply fpeq_refl]]]]]]]].
    apply GEN. intros E' He. cbn [fact_ok]. rewrite lden_laddc, He, u_Z_to_bv.
    assert (Hu : bv_unsigned (lden E l) = v + two64).
    { unfold eqm in Hv. rewrite (Z.mod_small (bv_unsigned (lden E l))) in Hv by exact Ul.
      rewrite <- Hv. symmetry. apply (Z.mod_unique v two64 (-1)); [left; unfold two64 in *; lia | ring]. }
    rewrite Hu. replace (v + two64 + - fst w) with ((v - fst w) + 1 * two64) by ring. rewrite Z.mod_add by (unfold two64; lia).
    rewrite Z.mod_small by (unfold two64 in *; lia). lia.
  - exists K2, ms, E. split; [right; left; reflexivity|]. split; [apply ist_refl|].
    split; [|split; [intros x Hx; reflexivity|split; [intros; reflexivity|split; [reflexivity|split; [unfold K2; cbn [xs_st s_next]; apply Pos.le_refl|split; [reflexivity|split; [exact HxF | split; [exact Hxw | apply fpeq_refl]]]]]]]].
    apply GEN. intros E' He. cbn [fact_ok]. rewrite He.
    assert (Hu : bv_unsigned (lden E l) = v).
    { unfold eqm in Hv. rewrite (Z.mod_small (bv_unsigned (lden E l))) in Hv by exact Ul. rewrite <- Hv. apply Z.mod_small. lia. }
    rewrite Hu. lia.
Qed.
(* [comment removed for export] *)
Definition hx_ssign (pc k : Z) (X : xst) : option (list xst) :=
  let L := xs_st X in
  let l := rget (s_regs L) (rkz k) in
  let w := swin (s_facts L) l in
  if (Z.eqb (s_pc L) pc && sfit w && Z.ltb (fst w) 0 && Z.leb 0 (snd w))%bool then
    match fcond_lookup (s_facts L) BC_LT l (lconst 0) with
    | Some true => Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (- 1 - fst w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X)]
    | Some false => Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange l 0 (snd w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X)]
    | None => Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (snd w - fst w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X)]
    end
  else if (Z.eqb (s_pc L) pc && sfit w)%bool then
    Some [XST (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (snd w - fst w) :: s_facts L) (s_next L) (s_resv L)) (xs_x X)]
  else if Z.eqb (s_pc L) pc then Some [X] else None.
#[using="Type"] Theorem hx_ssign_ok_fp : forall pc k, hand_okx_fp segs xok (hx_ssign pc k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc k X Ks E ms m0 Hf Hd HxF Hxw Hm0. destruct X as [L XL]. unfold hx_ssign in Hf. cbn [xs_st xs_x] in *.
  set (l := rget (s_regs L) (rkz k)) in *. set (w := swin (s_facts L) l) in *.
  assert (IDENT : Some [XST L XL] = Some Ks -> exists K ms' E', In K Ks /\ isteps segs ms ms' /\ sden segs E' (xs_st K) ms' /\ agree (s_next (xs_st (XST L XL))) E E' /\
      (forall x, fr_pt E (s_rgs (xs_st (XST L XL))) x -> ms_mem ms' x = ms_mem ms x) /\
      shape (s_rgs (xs_st K)) = shape (s_rgs (xs_st (XST L XL))) /\ (s_next (xs_st (XST L XL)) <= s_next (xs_st K))%positive /\
      rtm (s_rgs (xs_st K)) = rtm (s_rgs (xs_st (XST L XL))) /\
      Forall (xfact_ok xok E' m0) (xs_x K) /\ forallb (xwf (s_next (xs_st K))) (xs_x K) = true /\ fpeq ms ms').
  { intros H. injection H as <-.
    exists (XST L XL), ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
    split; [exact Hd|]. split; [intros x Hx; reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|].
    split; [apply Pos.le_refl|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact Hxw | apply fpeq_refl]. }
  pose proof (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _ & _ & HF & _).
  (* [comment removed for export] *)
  assert (WIN : sfit w = true -> forall E', lden E' l = lden E l -> fact_ok E' (FRange (laddc l (- fst w)) 0 (snd w - fst w))).
  { intros Hsf E' He. cbn [fact_ok].
    pose proof (swin_signed E (s_facts L) l HF Hsf) as Sw. fold w in Sw.
    pose proof Hsf as Hsf'. unfold sfit in Hsf'. apply andb_prop in Hsf' as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
    destruct (signed_eqm (lden E l)) as [Es Rs].
    rewrite lden_laddc, He, u_Z_to_bv. unfold eqm in Es.
    assert (X : (bv_unsigned (lden E l) + - fst w) mod two64 = (bv_signed (lden E l) - fst w) mod two64).
    { rewrite Zplus_mod, <- Es, <- Zplus_mod. replace (bv_signed (lden E l) + - fst w) with (bv_signed (lden E l) - fst w) by ring. reflexivity. }
    assert (X1 : 0 <= bv_signed (lden E l) - fst w < two64) by (unfold two64, T63 in *; lia).
    rewrite X, (Z.mod_small _ _ X1). lia. }
  destruct (Z.eqb (s_pc L) pc && sfit w && Z.ltb (fst w) 0 && Z.leb 0 (snd w))%bool eqn:Hc.
  2: { destruct (Z.eqb (s_pc L) pc && sfit w)%bool eqn:Hc2.
       - injection Hf as <-. apply andb_prop in Hc2 as [_ Hsf].
         assert (GEN0 : sden segs E (SST (s_pc L) (s_regs L) (s_rgs L) (FRange (laddc l (- fst w)) 0 (snd w - fst w) :: s_facts L) (s_next L) (s_resv L)) ms).
         { intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
           unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
           refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
           constructor; [|exact HF0]. apply (WIN Hsf).
           pose proof (HR0 (Z_to_bv 5 k)) as X1. pose proof (HR (Z_to_bv 5 k)) as X2. unfold l, rkz. rewrite <- X1, <- X2. reflexivity. }
         eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
         split; [exact GEN0|]. split; [intros x Hx; reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|].
         split; [apply Pos.le_refl|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact Hxw | apply fpeq_refl].
       - destruct (Z.eqb (s_pc L) pc); [exact (IDENT Hf) | discriminate]. }
  apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hc Hw1]. apply andb_prop in Hc as [_ Hsf].
  apply Z.ltb_lt in Hw1. apply Z.leb_le in Hw2.
  assert (GEN : forall f, (forall E', lden E' l = lden E l -> fact_ok E' f) ->
                  sden segs E (SST (s_pc L) (s_regs L) (s_rgs L) (f :: s_facts L) (s_next L) (s_resv L)) ms).
  { intros f Hfo E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
    refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj HG0 (conj HD0 (conj _ Hfrm0))))))).
    constructor; [|exact HF0]. apply Hfo.
    pose proof (HR0 (Z_to_bv 5 k)) as X1. pose proof (HR (Z_to_bv 5 k)) as X2. unfold l, rkz. rewrite <- X1, <- X2. reflexivity. }
  pose proof (swin_signed E (s_facts L) l HF Hsf) as Sw. fold w in Sw.
  pose proof Hsf as Hsf'. unfold sfit in Hsf'. apply andb_prop in Hsf' as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
  destruct (signed_eqm (lden E l)) as [Es Rs]. pose proof (u_range E l) as Ul.
  assert (ONE : forall f, (forall E', lden E' l = lden E l -> fact_ok E' f) ->
            exists K ms' E', In K [XST (SST (s_pc L) (s_regs L) (s_rgs L) (f :: s_facts L) (s_next L) (s_resv L)) XL] /\ isteps segs ms ms' /\
              sden segs E' (xs_st K) ms' /\ agree (s_next (xs_st (XST L XL))) E E' /\
              (forall x, fr_pt E (s_rgs (xs_st (XST L XL))) x -> ms_mem ms' x = ms_mem ms x) /\
              shape (s_rgs (xs_st K)) = shape (s_rgs (xs_st (XST L XL))) /\ (s_next (xs_st (XST L XL)) <= s_next (xs_st K))%positive /\
              rtm (s_rgs (xs_st K)) = rtm (s_rgs (xs_st (XST L XL))) /\
              Forall (xfact_ok xok E' m0) (xs_x K) /\ forallb (xwf (s_next (xs_st K))) (xs_x K) = true /\ fpeq ms ms').
  { intros f Hfo. eexists. exists ms, E. split; [left; reflexivity|]. split; [apply ist_refl|].
    split; [apply GEN; exact Hfo|]. split; [intros x Hx; reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|].
    split; [apply Pos.le_refl|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact Hxw | apply fpeq_refl]. }
  destruct (fcond_lookup (s_facts L) BC_LT l (lconst 0)) as [[|]|] eqn:Hl.
  - injection Hf as <-. apply ONE. intros E' He. cbn [fact_ok].
    pose proof (fcond_lookup_sound E (s_facts L) BC_LT l (lconst 0) true HF Hl) as Hb. cbn [branch_taken] in Hb.
    unfold bv_lts in Hb. rewrite lden_lconst in Hb. apply Z.ltb_lt in Hb.
    replace (bv_signed (Z_to_bv 64 0)) with 0 in Hb by reflexivity.
    rewrite lden_laddc, He, u_Z_to_bv.
    assert (Hu : bv_unsigned (lden E l) = bv_signed (lden E l) + two64).
    { unfold eqm in Es. rewrite (Z.mod_small (bv_unsigned (lden E l))) in Es by exact Ul.
      rewrite <- Es. symmetry. apply (Z.mod_unique (bv_signed (lden E l)) two64 (-1)); [left; unfold two64, T63 in *; lia | ring]. }
    rewrite Hu. replace (bv_signed (lden E l) + two64 + - fst w) with ((bv_signed (lden E l) - fst w) + 1 * two64) by ring.
    rewrite Z.mod_add by (unfold two64; lia).
    rewrite Z.mod_small by (unfold two64, T63 in *; lia). lia.
  - injection Hf as <-. apply ONE. intros E' He. cbn [fact_ok].
    pose proof (fcond_lookup_sound E (s_facts L) BC_LT l (lconst 0) false HF Hl) as Hb. cbn [branch_taken] in Hb.
    unfold bv_lts in Hb. rewrite lden_lconst in Hb. apply Z.ltb_ge in Hb.
    replace (bv_signed (Z_to_bv 64 0)) with 0 in Hb by reflexivity.
    rewrite He.
    assert (Hu : bv_unsigned (lden E l) = bv_signed (lden E l)).
    { unfold eqm in Es. rewrite (Z.mod_small (bv_unsigned (lden E l))) in Es by exact Ul.
      rewrite <- Es. apply Z.mod_small. unfold two64, T63 in *. lia. }
    rewrite Hu. lia.
  - injection Hf as <-. apply ONE. exact (WIN Hsf).
Qed.
End HxGenFp.
