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

Module FxExplore.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep FxSubst.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma fx_step_sbr_inv : forall t img s c a b tgt, fx_step t img s = SBr c a b tgt ->
  exists rs1 rs2, tlookup t (s_pc s) = XBr c rs1 rs2 tgt /\ a = rget (s_regs s) rs1 /\ b = rget (s_regs s) rs2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s c a b tgt H. unfold fx_step in H.
  destruct (tlookup t (s_pc s)) eqn:Hx;
    repeat match type of H with
    | context [match ?e with _ => _ end] => destruct e eqn:?; try discriminate
    end; try discriminate.
  injection H as <- <- <- <-. exists rs1, rs2. split; [first [exact Hx | reflexivity] | split; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fx_step_br_fp : forall t img s c a b tgt E ms,
  tbl_ok segs t -> fx_step t img s = SBr c a b tgt -> sden segs E s ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_svc_pending ms = None /\
    sden segs E (with_pc_fact s (if branch_taken c (lden E a) (lden E b) then tgt else s_pc s + 4)
                   (FCond c a b (branch_taken c (lden E a) (lden E b)))) ms' /\ ms_mem ms' = ms_mem ms /\ fpeq ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s c a b tgt E ms Ht Hstep Hden.
  pose proof (sden_0 _ _ _ _ Hden) as Hd0.
  destruct Hd0 as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  pose proof (mks_eta ms Hsvc) as Hms. rewrite Hpc in Hms.
  destruct (fx_step_sbr_inv t img s c a b tgt Hstep) as (rs1 & rs2 & Hx & -> & ->).
  destruct (Ht (s_pc s) _ Hx ltac:(discriminate) ltac:(discriminate)) as (w & i & Hfetch & Hecall & Hdecode & Hxl).
  destruct (xl_br _ _ _ _ _ _ Hxl) as (ra & rb & im & -> & -> & -> & ->).
  rewrite <- (HR ra), <- (HR rb).
  assert (Hst0 : RiscvSemantics.step segs ms = RiscvSemantics.step segs (mks (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (Z_to_bv 64 (s_pc s)) (ms_resv ms) (ms_mem ms) (ms_rom ms)))
    by (f_equal; exact Hms).
  rewrite Hst0. eexists. split; [eapply g_branch; eassumption|]. split; [exact Hsvc|]. split; [|split; [reflexivity | split; [intros ?r; reflexivity | reflexivity]]].
  intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & Hrv'' & HR'' & HG'' & HD'' & HF'' & _).
  unfold with_pc_fact, sden0; cbn [s_pc s_regs s_rgs s_facts s_resv ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr mks].
  split; [ destruct (branch_taken c (getr (ms_regs ms) ra) (getr (ms_regs ms) rb)); [symmetry; apply Z_to_bv_bv_unsigned | apply pc_plus4] |].
  split; [reflexivity|]. split; [exact Hrv''|]. split; [exact HR''|]. split; [exact HG''|]. split; [exact HD''|].
  split; [|exact Hfrm].
  constructor; [|exact HF'']. cbn [fact_ok]. rewrite <- (HR'' ra), <- (HR'' rb). reflexivity.
Qed.

#[using="Type"] Lemma fx_step_br : forall t img s c a b tgt E ms,
  tbl_ok segs t -> fx_step t img s = SBr c a b tgt -> sden segs E s ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_svc_pending ms = None /\
    sden segs E (with_pc_fact s (if branch_taken c (lden E a) (lden E b) then tgt else s_pc s + 4)
                   (FCond c a b (branch_taken c (lden E a) (lden E b)))) ms' /\ ms_mem ms' = ms_mem ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s c a b tgt E ms Ht Hs Hd. destruct (fx_step_br_fp t img s c a b tgt E ms Ht Hs Hd) as (ms' & H1 & H2 & H3 & H4 & _).
  exists ms'. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fx_step_br_fpc : forall t img s c a b tgt E ms ms',
  tbl_ok segs t -> fx_step t img s = SBr c a b tgt -> sden segs E s ms -> RiscvSemantics.step segs ms = MachineOk ms' -> fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s c a b tgt E ms ms' Ht Hs Hd Hst _. destruct (fx_step_br_fp t img s c a b tgt E ms Ht Hs Hd) as (ms1 & H1 & _ & _ & _ & Hfp).
  rewrite Hst in H1. injection H1 as <-. exact Hfp.
Qed.

#[using="Type"] Lemma explore_acc : forall t img fuel stops s acc L, In L acc -> In L (fx_explore t img fuel stops s acc).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel. induction fuel as [|f IH]; intros stops s acc L HL; cbn [fx_explore].
  - right. exact HL.
  - destruct (fx_step t img s) as [s'| c a b tgt | l c |].
    + destruct (existsb (Z.eqb (s_pc s')) stops); [right; exact HL | apply IH; exact HL].
    + assert (H1 : In L (if existsb (Z.eqb (s_pc (with_pc_fact s tgt (FCond c a b true)))) stops
                         then with_pc_fact s tgt (FCond c a b true) :: acc
                         else fx_explore t img f stops (with_pc_fact s tgt (FCond c a b true)) acc)).
      { destruct (existsb _ stops); [right; exact HL | apply IH; exact HL]. }
      destruct (existsb (Z.eqb (s_pc (with_pc_fact s (s_pc s + 4) (FCond c a b false)))) stops); [right; exact H1 | apply IH; exact H1].
    + apply IH. apply IH. exact HL.
    + right. exact HL.
Qed.

#[using="Type"] Lemma fx_step_split_inv : forall t img s l c, fx_step t img s = SSplit l c -> lclosed (s_next s) l = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s l c H. unfold fx_step in H.
  destruct (tlookup t (s_pc s)) eqn:Hx;
    repeat match type of H with
    | context [match ?e with _ => _ end] => destruct e eqn:?; try discriminate
    end; try discriminate;
    try (injection H as <- <-; assumption).
Qed.

#[using="Type"] Lemma split_child : forall E s ms l c tk, sden segs E s ms -> lclosed (s_next s) l = true ->
  branch_taken BC_LTU (lden E l) (lden E (lconst c)) = tk ->
  sden segs E (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) tk)) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms l c tk Hden Hcl Htk E'' Ha''. destruct (Hden E'' Ha'') as (Hpc & Hsvc & Hrv & HR & HG & HD & HF & Hfrm).
  unfold with_pc_fact, sden0. cbn [s_pc s_regs s_rgs s_facts s_resv].
  split; [exact Hpc|]. split; [exact Hsvc|]. split; [exact Hrv|]. split; [exact HR|]. split; [exact HG|]. split; [exact HD|].
  split; [|exact Hfrm]. constructor; [|exact HF]. cbn [fact_ok].
  change (lclosed (s_next s) l) with (lwf (s_next s) l) in Hcl.
  rewrite <- (lden_agree (s_next s) E E'' l Hcl Ha''). rewrite !lden_lconst in *. exact Htk.
Qed.

#[using="Type"] Theorem explore_sound_fp : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel. induction fuel as [|f IH]; intros stops s acc E ms Ht Himg Hden; cbn [fx_explore].
  - exists s, ms, E. split; [left; reflexivity|]. split; [constructor | split; [exact Hden | split; [apply agree_refl | apply fpc_refl]]].
  - destruct (fx_step t img s) as [s'| c a b tgt | l c |] eqn:Hs.
    + destruct (fx_step_sound segs t img s s' E ms Ht Himg Hs Hden) as (ms1 & E1 & Hst & Hsvc & Ha1 & Hn1 & Hd1 & _ & _).
      pose proof (fx_step_fpc segs t img s s' E ms ms1 Ht Himg Hs Hden Hst) as Hfp1.
      destruct (existsb (Z.eqb (s_pc s')) stops).
      * exists s', ms1, E1. split; [left; reflexivity|]. split; [econstructor; [exact Hsvc | exact Hst | constructor] | split; [exact Hd1 | split; [exact Ha1 | exact Hfp1]]].
      * destruct (IH stops s' acc E1 ms1 Ht Himg Hd1) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfp2).
        exists L, ms2, E2. split; [exact HL|]. split; [econstructor; [exact Hsvc | exact Hst | exact Hst2] | split; [exact Hd2|]].
        split; [eapply agree_trans; [exact Ha1 | eapply agree_mono; [exact Hn1 | exact Ha2]] | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)].
    + destruct (fx_step_br t img s c a b tgt E ms Ht Hs Hden) as (ms1 & Hst & Hsvc & Hd1 & _).
      pose proof (fx_step_br_fpc t img s c a b tgt E ms ms1 Ht Hs Hden Hst) as Hfp1.
      set (s1 := with_pc_fact s tgt (FCond c a b true)). set (s2 := with_pc_fact s (s_pc s + 4) (FCond c a b false)).
      set (acc1 := if existsb (Z.eqb (s_pc s1)) stops then s1 :: acc else fx_explore t img f stops s1 acc).
      assert (Hfin : forall L, In L acc1 -> In L (if existsb (Z.eqb (s_pc s2)) stops then s2 :: acc1 else fx_explore t img f stops s2 acc1)).
      { intros L HL. destruct (existsb (Z.eqb (s_pc s2)) stops); [right; exact HL | apply explore_acc; exact HL]. }
      destruct (branch_taken c (lden E a) (lden E b)) eqn:Htk.
      * (* [comment removed for export] *)
        assert (Hx : exists L ms2 E2, In L acc1 /\ isteps segs ms1 ms2 /\ sden segs E2 L ms2 /\ agree (s_next s) E E2 /\ fpc t ms1 ms2).
        { unfold acc1. destruct (existsb (Z.eqb (s_pc s1)) stops).
          - exists s1, ms1, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hd1 | split; [apply agree_refl | apply fpc_refl]].
          - destruct (IH stops s1 acc E ms1 Ht Himg Hd1) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfp2).
            exists L, ms2, E2. split; [exact HL|]. split; [exact Hst2|]. split; [exact Hd2 | split; [exact Ha2 | exact Hfp2]]. }
        destruct Hx as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfp2).
        exists L, ms2, E2. split; [apply Hfin; exact HL|].
        split; [econstructor; [exact Hsvc | exact Hst | exact Hst2] | split; [exact Hd2 | split; [exact Ha2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]].
      * (* [comment removed for export] *)
        destruct (existsb (Z.eqb (s_pc s2)) stops) eqn:Hs2.
        -- exists s2, ms1, E. split; [left; reflexivity|]. split; [econstructor; [exact Hsvc | exact Hst | constructor]|].
           split; [exact Hd1 | split; [apply agree_refl | exact Hfp1]].
        -- destruct (IH stops s2 acc1 E ms1 Ht Himg Hd1) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfp2).
           exists L, ms2, E2. split; [exact HL|].
           split; [econstructor; [exact Hsvc | exact Hst | exact Hst2] | split; [exact Hd2 | split; [exact Ha2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]]].
    + pose proof (fx_step_split_inv t img s l c Hs) as Hcl.
      destruct (branch_taken BC_LTU (lden E l) (lden E (lconst c))) eqn:Htk.
      * destruct (IH stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true)) acc E ms Ht Himg (split_child E s ms l c true Hden Hcl Htk))
          as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfp2).
        exists L, ms2, E2. split; [apply explore_acc; exact HL|]. split; [exact Hst2 | split; [exact Hd2 | split; [exact Ha2 | exact Hfp2]]].
      * destruct (IH stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) false)) (fx_explore t img f stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true)) acc)
                     E ms Ht Himg (split_child E s ms l c false Hden Hcl Htk))
          as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfp2).
        exists L, ms2, E2. split; [exact HL|]. split; [exact Hst2 | split; [exact Hd2 | split; [exact Ha2 | exact Hfp2]]].
    + exists s, ms, E. split; [left; reflexivity|]. split; [constructor | split; [exact Hden | split; [apply agree_refl | apply fpc_refl]]].
Qed.
#[using="Type"] Theorem explore_sound : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops s acc E ms Ht Himg Hd.
  destruct (explore_sound_fp t img fuel stops s acc E ms Ht Himg Hd) as (L & ms' & E' & H1 & H2 & H3 & H4 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lwf_mono : forall n n' l, (n <= n')%positive -> lwf n l = true -> lwf n' l = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n n' [c t] Hn H. unfold lwf in *; cbn [l_t] in *. rewrite forallb_forall in *. intros [x k] Hx.
  specialize (H (x, k) Hx). apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
Qed.

Definition bases_wf (n : positive) (rgs : list region) : bool := forallb (fun R => lwf n (rg_base R) && lwf n (rg_size R))%bool rgs.

#[using="Type"] Lemma bases_wf_shape : forall n n' rgs rgs', (n <= n')%positive -> shape rgs' = shape rgs -> bases_wf n rgs = true -> bases_wf n' rgs' = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n n' rgs. induction rgs as [|R rs IH]; intros [|R' rs'] Hn Hs H; cbn in *; try discriminate; [reflexivity|].
  injection Hs as Hb Hsz Hrs. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H1s]. apply andb_true_intro. split.
  - rewrite Hb, Hsz. apply andb_true_intro. split; [exact (lwf_mono _ _ _ Hn H1) | exact (lwf_mono _ _ _ Hn H1s)].
  - exact (IH rs' Hn Hrs H2).
Qed.

#[using="Type"] Lemma outside_agree : forall n E E' rgs x, bases_wf n rgs = true -> agree n E E' -> (outside E rgs x <-> outside E' rgs x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' rgs x H Ha. unfold outside, bases_wf in *. rewrite forallb_forall in H.
  split; intros HF; apply Forall_forall; intros R0 HR0; rewrite Forall_forall in HF; specialize (HF R0 HR0); cbv beta in *;
    destruct (andb_prop _ _ (H R0 HR0)) as [Hb0 Hs0]; unfold rsz in *;
    pose proof (lden_agree n E E' _ Hb0 Ha) as He; pose proof (lden_agree n E E' _ Hs0 Ha) as Hes;
    rewrite ?He, ?Hes in *; rewrite <- ?He, <- ?Hes in *; exact HF.
Qed.

#[using="Type"] Lemma outside_shape : forall E rgs rgs' x, shape rgs' = shape rgs -> outside E rgs x -> outside E rgs' x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs. induction rgs as [|R rs IH]; intros [|R' rs'] x Hs H; cbn in *; try discriminate; [constructor|].
  injection Hs as Hb Hsz Hrs. inversion H; subst. constructor; [unfold rsz in *; rewrite Hb, Hsz; assumption | exact (IH rs' x Hrs H3)].
Qed.

#[using="Type"] Theorem explore_frame_fp : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    (forall x, outside E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel. induction fuel as [|f IH]; intros stops s acc E ms Ht Himg Hden Hwf; cbn [fx_explore].
  - exists s, ms, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hden|]. split; [apply agree_refl|].
    split; [intros; reflexivity | split; [reflexivity | apply fpc_refl]].
  - destruct (fx_step t img s) as [s'| c a b tgt | l c |] eqn:Hs.
    + destruct (fx_step_sound segs t img s s' E ms Ht Himg Hs Hden) as (ms1 & E1 & Hst & Hsvc & Ha1 & Hn1 & Hd1 & Hfr1 & Hsh1).
      pose proof (fx_step_fpc segs t img s s' E ms ms1 Ht Himg Hs Hden Hst) as Hfp1.
      assert (Hwf1 : bases_wf (s_next s') (s_rgs s') = true) by exact (bases_wf_shape _ _ _ _ Hn1 Hsh1 Hwf).
      destruct (existsb (Z.eqb (s_pc s')) stops).
      * exists s', ms1, E1. split; [left; reflexivity|]. split; [econstructor; [exact Hsvc | exact Hst | constructor]|].
        split; [exact Hd1|]. split; [exact Ha1|]. split; [exact Hfr1 | split; [exact Hsh1 | exact Hfp1]].
      * destruct (IH stops s' acc E1 ms1 Ht Himg Hd1 Hwf1) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hfp2).
        exists L, ms2, E2. split; [exact HL|]. split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [exact Hd2|].
        split; [eapply agree_trans; [exact Ha1 | eapply agree_mono; [exact Hn1 | exact Ha2]]|].
        split; [|split; [rewrite Hsh2; exact Hsh1 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]].
        intros x Hx. rewrite Hfr2; [exact (Hfr1 x Hx)|].
        apply (outside_agree (s_next s) E E1 (s_rgs s') x); [exact (bases_wf_shape _ _ _ _ (Pos.le_refl _) Hsh1 Hwf) | exact Ha1 |].
        exact (outside_shape E _ _ x Hsh1 Hx).
    + destruct (fx_step_br t img s c a b tgt E ms Ht Hs Hden) as (ms1 & Hst & Hsvc & Hd1 & Hm1).
      pose proof (fx_step_br_fpc t img s c a b tgt E ms ms1 Ht Hs Hden Hst) as Hfp1.
      set (s1 := with_pc_fact s tgt (FCond c a b true)). set (s2 := with_pc_fact s (s_pc s + 4) (FCond c a b false)).
      set (acc1 := if existsb (Z.eqb (s_pc s1)) stops then s1 :: acc else fx_explore t img f stops s1 acc).
      assert (Hfin : forall L, In L acc1 -> In L (if existsb (Z.eqb (s_pc s2)) stops then s2 :: acc1 else fx_explore t img f stops s2 acc1)).
      { intros L HL. destruct (existsb (Z.eqb (s_pc s2)) stops); [right; exact HL | apply explore_acc; exact HL]. }
      assert (Hwfb : forall sb, s_rgs sb = s_rgs s -> s_next sb = s_next s -> bases_wf (s_next sb) (s_rgs sb) = true)
        by (intros sb H1 H2; rewrite H1, H2; exact Hwf).
      destruct (branch_taken c (lden E a) (lden E b)) eqn:Htk.
      * assert (Hx : exists L ms2 E2, In L acc1 /\ isteps segs ms1 ms2 /\ sden segs E2 L ms2 /\ agree (s_next s) E E2 /\
                       (forall x, outside E (s_rgs s) x -> ms_mem ms2 x = ms_mem ms1 x) /\ shape (s_rgs L) = shape (s_rgs s) /\ fpc t ms1 ms2).
        { unfold acc1. destruct (existsb (Z.eqb (s_pc s1)) stops).
          - exists s1, ms1, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hd1|]. split; [apply agree_refl|].
            split; [intros; reflexivity | split; [reflexivity | apply fpc_refl]].
          - destruct (IH stops s1 acc E ms1 Ht Himg Hd1 (Hwfb s1 eq_refl eq_refl)) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hfp2).
            exists L, ms2, E2. split; [exact HL|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Ha2|].
            split; [exact Hfr2 | split; [exact Hsh2 | exact Hfp2]]. }
        destruct Hx as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hfp2).
        exists L, ms2, E2. split; [apply Hfin; exact HL|].
        split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [exact Hd2|]. split; [exact Ha2|].
        split; [intros x Hx; rewrite Hfr2, Hm1 by exact Hx; reflexivity | split; [exact Hsh2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]].
      * destruct (existsb (Z.eqb (s_pc s2)) stops) eqn:Hs2.
        -- exists s2, ms1, E. split; [left; reflexivity|]. split; [econstructor; [exact Hsvc | exact Hst | constructor]|].
           split; [exact Hd1|]. split; [apply agree_refl|]. split; [intros x Hx; rewrite Hm1; reflexivity | split; [reflexivity | exact Hfp1]].
        -- destruct (IH stops s2 acc1 E ms1 Ht Himg Hd1 (Hwfb s2 eq_refl eq_refl)) as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hfp2).
           exists L, ms2, E2. split; [exact HL|].
           split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [exact Hd2|]. split; [exact Ha2|].
           split; [intros x Hx; rewrite Hfr2, Hm1 by exact Hx; reflexivity | split; [exact Hsh2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]].
    + pose proof (fx_step_split_inv t img s l c Hs) as Hcl.
      destruct (branch_taken BC_LTU (lden E l) (lden E (lconst c))) eqn:Htk.
      * destruct (IH stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true)) acc E ms Ht Himg (split_child E s ms l c true Hden Hcl Htk) Hwf)
          as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hfp2).
        exists L, ms2, E2. split; [apply explore_acc; exact HL|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Ha2|].
        split; [exact Hfr2 | split; [exact Hsh2 | exact Hfp2]].
      * destruct (IH stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) false)) (fx_explore t img f stops (with_pc_fact s (s_pc s) (FCond BC_LTU l (lconst c) true)) acc)
                     E ms Ht Himg (split_child E s ms l c false Hden Hcl Htk) Hwf)
          as (L & ms2 & E2 & HL & Hst2 & Hd2 & Ha2 & Hfr2 & Hsh2 & Hfp2).
        exists L, ms2, E2. split; [exact HL|]. split; [exact Hst2|]. split; [exact Hd2|]. split; [exact Ha2|].
        split; [exact Hfr2 | split; [exact Hsh2 | exact Hfp2]].
    + exists s, ms, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hden|]. split; [apply agree_refl|].
      split; [intros; reflexivity | split; [reflexivity | apply fpc_refl]].
Qed.
#[using="Type"] Theorem explore_frame : forall t img fuel stops s acc E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms -> bases_wf (s_next s) (s_rgs s) = true ->
  exists L ms' E', In L (fx_explore t img fuel stops s acc) /\ isteps segs ms ms' /\ sden segs E' L ms' /\ agree (s_next s) E E' /\
    (forall x, outside E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs L) = shape (s_rgs s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops s acc E ms Ht Himg Hd Hw.
  destruct (explore_frame_fp t img fuel stops s acc E ms Ht Himg Hd Hw) as (L & ms' & E' & H1 & H2 & H3 & H4 & H5 & H6 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

End WithSegs.
End FxExplore.

From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.

Module AcShift.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxSubst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition vshift (n : positive) (E : valu) : valu := fun y => E (n + y)%positive.
Definition tshift (n : positive) (t : list (positive * Z)) : list (positive * Z) :=
  List.map (fun p => ((n + fst p)%positive, snd p)) t.
Definition lshift (n : positive) (l : lin) : lin := LIN (l_c l) (tshift n (l_t l)).
Definition bshift (n : positive) (v : bval) : bval := match v with BK b => BK b | BV l j => BV (lshift n l) j end.
Definition fshift (n : positive) (f : fact) : fact :=
  match f with
  | FCond c a b tk => FCond c (lshift n a) (lshift n b) tk
  | FRange l lo hi => FRange (lshift n l) lo hi
  | FMod l k r => FMod (lshift n l) k r
  | FBits l m v => FBits (lshift n l) m v
  | FByte x v j => FByte (lshift n x) (lshift n v) j
  | FBytes x bs => FBytes (lshift n x) (List.map (fun p => (lshift n (fst p), snd p)) bs)
  end.
Definition rshift (n : positive) (R : region) : region :=
  RG (lshift n (rg_base R)) (lshift n (rg_size R)) (rg_kind R) (tmap (bshift n) (rg_cont R)).
Definition rsv_shift (n : positive) (r : rsv) : rsv := match r with RAt l => RAt (lshift n l) | _ => r end.
Definition sst_shift (n : positive) (P : sst) : sst :=
  SST (s_pc P) (tmap (lshift n) (s_regs P)) (List.map (rshift n) (s_rgs P)) (List.map (fshift n) (s_facts P))
      (n + s_next P)%positive (rsv_shift n (s_resv P)).

(* [comment removed for export] *)
Lemma tsum_shift : forall n E t, tsum E (tshift n t) = tsum (vshift n E) t.
Proof. intros n E t. induction t as [|[x c] t IH]; cbn [tshift List.map tsum fst snd]; [reflexivity|]. rewrite <- IH. reflexivity. Qed.
Lemma lden_shift : forall n E l, lden E (lshift n l) = lden (vshift n E) l.
Proof. intros n E [c t]. unfold lden, lz, lshift. cbn [l_c l_t]. rewrite tsum_shift. reflexivity. Qed.
Lemma bden_shift : forall n E v, bden E (bshift n v) = bden (vshift n E) v.
Proof. intros n E [b|l j]; cbn [bshift bden]; [reflexivity | rewrite lden_shift; reflexivity]. Qed.
Lemma rget_shift : forall n R k, rget (tmap (lshift n) R) k = lshift n (rget R k).
Proof.
  intros n R k. unfold rget. destruct k as [p|p|]; [| |reflexivity]; rewrite tget_tmap; destruct (tget _ R); reflexivity.
Qed.
Lemma rsz_shift : forall n E R, rsz E (rshift n R) = rsz (vshift n E) R.
Proof. intros n E R. unfold rsz, rshift. cbn [rg_size]. rewrite lden_shift. reflexivity. Qed.
Lemma base_shift : forall n E R, lden E (rg_base (rshift n R)) = lden (vshift n E) (rg_base R).
Proof. intros n E R. unfold rshift. cbn [rg_base]. apply lden_shift. Qed.

Lemma regs_ok_shift : forall n E R regs, regs_ok E (tmap (lshift n) R) regs <-> regs_ok (vshift n E) R regs.
Proof.
  intros n E R regs. unfold regs_ok. split; intros H r; rewrite (H r); rewrite rget_shift, lden_shift; reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ok_shift : forall n E m R, rg_ok segs E m (rshift n R) <-> rg_ok segs (vshift n E) m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E m R. unfold rg_ok. rewrite rsz_shift, base_shift. cbn [rg_kind rshift rg_cont].
  split; intros (H1 & H2 & H3 & H4); (split; [exact H1|]); (split; [exact H2|]); split.
  - intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3;
      (destruct H3 as [H3a H3b]; split; [exact H3a|]; intros Hn; apply H3b; rewrite tget_tmap, Hn; reflexivity).
  - intros p v Hp. destruct (H4 p (bshift n v)) as [Ha Hb]; [rewrite tget_tmap, Hp; reflexivity|].
    split; [exact Ha|]. rewrite bden_shift in Hb. exact Hb.
  - intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3;
      (destruct H3 as [H3a H3b]; split; [exact H3a|]; intros Hn; apply H3b; rewrite tget_tmap in Hn;
       destruct (tget (okey i) (rg_cont R)); [discriminate | reflexivity]).
  - intros p v Hp. rewrite tget_tmap in Hp. destruct (tget p (rg_cont R)) as [v0|] eqn:E0; [|discriminate].
    cbn [option_map] in Hp. injection Hp as <-. destruct (H4 p v0 E0) as [Ha Hb]. split; [exact Ha|].
    rewrite bden_shift. exact Hb.
Qed.

#[using="Type"] Lemma rg_disj_shift : forall n E R1 R2, rg_disj E (rshift n R1) (rshift n R2) <-> rg_disj (vshift n E) R1 R2.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E R1 R2. unfold rg_disj. rewrite !base_shift, !rsz_shift. tauto. Qed.

#[using="Type"] Lemma rgs_disj_shift : forall n E rgs, rgs_disj E (List.map (rshift n) rgs) <-> rgs_disj (vshift n E) rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E rgs. induction rgs as [|R rs IH]; cbn [List.map rgs_disj]; [tauto|]. rewrite IH.
  rewrite Forall_map. split; intros [H1 H2]; split; try exact H2;
    (eapply Forall_impl; [|exact H1]); intros R' HR'; apply rg_disj_shift; exact HR'.
Qed.

#[using="Type"] Lemma fact_ok_shift : forall n E f, fact_ok E (fshift n f) <-> fact_ok (vshift n E) f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E [c a b tk|l lo hi|l k r|l m v|x v j|x bs]; cbn [fshift fact_ok]; rewrite ?lden_shift; try tauto.
  rewrite length_map.
  assert (Hn : forall i, nth i (List.map (fun p => (lshift n (fst p), snd p)) bs) (lconst 0, 0) = (lshift n (fst (nth i bs (lconst 0, 0))), snd (nth i bs (lconst 0, 0)))).
  { intros i. change (lconst 0, 0) with ((fun p : lin * Z => (lshift n (fst p), snd p)) (lconst 0, 0)) at 1. rewrite map_nth. reflexivity. }
  split; intros H i Hi; specialize (H i Hi); rewrite ?Hn in *; cbn [fst snd] in *; rewrite ?lden_shift in *; exact H.
Qed.

#[using="Type"] Lemma rsv_ok_shift : forall n E r v, rsv_ok E (rsv_shift n r) v <-> rsv_ok (vshift n E) r v.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E [|l|] v; cbn [rsv_shift rsv_ok]; rewrite ?lden_shift; tauto. Qed.

#[using="Type"] Theorem sden0_shift : forall n E P ms, sden0 segs E (sst_shift n P) ms <-> sden0 segs (vshift n E) P ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E P ms. unfold sden0, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_resv].
  rewrite regs_ok_shift, rsv_ok_shift, rgs_disj_shift, !Forall_map.
  assert (HG : Forall (fun R => rg_ok segs E (ms_mem ms) (rshift n R)) (s_rgs P) <-> Forall (rg_ok segs (vshift n E) (ms_mem ms)) (s_rgs P)).
  { split; intros H; (eapply Forall_impl; [|exact H]); intros R HR; apply rg_ok_shift; exact HR. }
  assert (HF : Forall (fun f => fact_ok E (fshift n f)) (s_facts P) <-> Forall (fact_ok (vshift n E)) (s_facts P)).
  { split; intros H; (eapply Forall_impl; [|exact H]); intros f Hf; apply fact_ok_shift; exact Hf. }
  rewrite HG, HF. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem sden_shift_fwd : forall n E P ms, state_wf P = true -> sden0 segs E (sst_shift n P) ms -> sden segs (vshift n E) P ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E P ms Hw H. apply sden0_sden; [exact Hw|]. apply sden0_shift. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem sden_shift_bwd : forall n E E1 L ms, sden segs E1 L ms -> agree (s_next L) E1 (vshift n E) ->
  sden0 segs E (sst_shift n L) ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E E1 L ms H Ha. apply sden0_shift. exact (H _ Ha). Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma lwf_shift : forall n m l, lwf m l = true -> lwf (n + m) (lshift n l) = true.
Proof.
  intros n m [c t] H. unfold lwf, lshift in *. cbn [l_t] in *. unfold tshift.
  rewrite forallb_forall in *. intros [x k] Hx. apply in_map_iff in Hx as ([y k'] & Hy & Hin). cbn [fst snd] in Hy. injection Hy as <- <-.
  specialize (H _ Hin). cbn in H. apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
Qed.
Lemma lwf_shift_ge : forall n l, forallb (fun p => Pos.leb n (fst p)) (l_t (lshift n l)) = true.
Proof.
  intros n [c t]. unfold lshift, tshift. cbn [l_t]. rewrite forallb_forall. intros [x k] Hx.
  apply in_map_iff in Hx as ([y k'] & Hy & _). cbn [fst snd] in Hy. injection Hy as <- _. cbn [fst]. apply Pos.leb_le. lia.
Qed.
End AcShift.

Module FxQChk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition zeros8 : list byte := List.repeat (Z_to_bv 8 0) 8.
Lemma bytes_le_zeros8 : bytes_le_to_Z zeros8 = 0. Proof. reflexivity. Qed.

Ltac neq := first [assumption | apply not_eq_sym; assumption].
Ltac gsimp := repeat first [ rewrite getr_same by neq | rewrite getr_other by neq ].
Ltac nz_if := match goal with |- context [if bv_eqb ?r 0 then _ else _] =>
                replace (bv_eqb r 0%bv) with false by (symmetry; apply bv_eqb_neq; neq) end.

Section QC.
Context {fx : FPState}.
Variable segs : list Segment.
Variables (pc0 : Z) (rP rA rB rS rY rZ rW : reg) (ai : bv 20) (im1 : bv 12) (bim : bv 13) (beq : bool).
Hypothesis Hnz : rP <> 0%bv /\ rA <> 0%bv /\ rY <> 0%bv /\ rZ <> 0%bv /\ rW <> 0%bv.
Hypothesis Hd1 : rA <> rP /\ rY <> rP /\ rY <> rA /\ rZ <> rP /\ rZ <> rA /\ rZ <> rY /\ rW <> rP /\ rW <> rA /\ rW <> rY /\ rW <> rZ.
Hypothesis Hd2 : rB <> rP /\ rB <> rA /\ rB <> rY /\ rS <> rP.

Definition qpc (k : Z) : word := Z_to_bv 64 (pc0 + 4 * k).
Definition qins (k : Z) (i : instr) : Prop :=
  exists w, fetch_word segs (qpc k) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Hypothesis I0 : qins 0 (Auipc rP ai).
Hypothesis I1 : qins 1 (Load SZ8 true rP rP im1).
Hypothesis I2 : qins 2 (Op ALU_ADD rA rB rS).
Hypothesis I3 : qins 3 (Load SZ8 true rY rP (Z_to_bv 12 0)).
Hypothesis I4 : qins 4 (ShiftImm ALU_SRL rP rB (Z_to_bv 6 3)).
Hypothesis I5 : qins 5 (OpImm ALU_ADD rA rA (Z_to_bv 12 (-1))).
Hypothesis I6 : qins 6 (ShiftImm ALU_SRL rZ rA (Z_to_bv 6 3)).
Hypothesis I7 : qins 7 (Op ALU_ADD rP rY rP).
Hypothesis I8 : qins 8 (Op ALU_ADD rY rY rZ).
Hypothesis I9 : qins 9 (OpImm ALU_AND rZ rP (Z_to_bv 12 (-8))).
Hypothesis I10 : qins 10 (OpImm ALU_AND rW rY (Z_to_bv 12 (-8))).
Hypothesis I11 : qins 11 (Load SZ8 true rZ rZ (Z_to_bv 12 0)).
Hypothesis I12 : qins 12 (Load SZ8 true rW rW (Z_to_bv 12 0)).
Hypothesis I13 : qins 13 (Op ALU_OR rZ rW rZ).
Hypothesis I14 : qins 14 (Branch (if beq then BC_EQ else BC_NE) rZ (Z_to_bv 5 0) bim).

(* [comment removed for export] *)
Definition qok : word := if beq then btgt (qpc 14) (bv_signed bim) else qpc 15.
(* [comment removed for export] *)
Definition qG : word := v_addi (v_auipc (qpc 0) (Z.shiftl (bv_signed ai) 12)) (bv_signed im1).
Definition qlast (b : word) (n : Z) : word := v_addi (v_add b (Z_to_bv 64 n)) (-1).
Definition qX (sh b : word) : word := v_add sh (v_srli b 3).
Definition qY (sh b : word) (n : Z) : word := v_add sh (v_srli (qlast b n) 3).
Definition qw1 (sh b : word) : word := v_andi (qX sh b) (-8).
Definition qw2 (sh b : word) (n : Z) : word := v_andi (qY sh b n) (-8).

#[using="Type"] Lemma qpc_succ : forall k, v_addi (qpc k) 4 = qpc (k + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. unfold v_addi, qpc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
#[using="Type"] Lemma v_addi0 : forall x : word, v_addi x 0 = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.



(* [comment removed for export] *)
#[using="Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14"] Theorem qc_isteps : forall regs mem rom (b : word) (n : Z) (P sh : word) bsG bsP,
  getr regs rB = b -> getr regs rS = Z_to_bv 64 n ->
  rdn segs mem qG 8 = Some bsG -> bytes_le_to_Z bsG = bv_unsigned P ->
  rdn segs mem P 8 = Some bsP -> bytes_le_to_Z bsP = bv_unsigned sh ->
  rdn segs mem (qw1 sh b) 8 = Some zeros8 -> rdn segs mem (qw2 sh b n) 8 = Some zeros8 ->
  exists regs',
    FxStep.isteps segs (mkst regs (qpc 0) mem rom) (mkst regs' qok mem rom) /\
    getr regs' rP = qX sh b /\ getr regs' rY = qY sh b n /\ getr regs' rA = qlast b n /\
    getr regs' rZ = Z_to_bv 64 0 /\ getr regs' rW = Z_to_bv 64 0 /\
    (forall r, r <> rP -> r <> rA -> r <> rY -> r <> rZ -> r <> rW -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom b n P sh bsG bsP HB HS HG HGv HP HPv HW1 HW2.
  destruct Hnz as (NP & NA & NY & NZ & NW).
  destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
  destruct Hd2 as (DBP & DBA & DBY & DSP).
  destruct I0 as (w0 & F0 & E0 & D0). destruct I1 as (w1 & F1 & E1 & D1). destruct I2 as (w2 & F2 & E2 & D2).
  destruct I3 as (w3 & F3 & E3 & D3). destruct I4 as (w4 & F4 & E4 & D4). destruct I5 as (w5 & F5 & E5 & D5).
  destruct I6 as (w6 & F6 & E6 & D6). destruct I7 as (w7 & F7 & E7 & D7). destruct I8 as (w8 & F8 & E8 & D8).
  destruct I9 as (w9 & F9 & E9 & D9). destruct I10 as (w10 & F10 & E10 & D10). destruct I11 as (w11 & F11 & E11 & D11).
  destruct I12 as (w12 & F12 & E12 & D12). destruct I13 as (w13 & F13 & E13 & D13). destruct I14 as (w14 & F14 & E14 & D14).
  (* [comment removed for export] *)
  set (r1 := regupd regs rP (v_auipc (qpc 0) (Z.shiftl (bv_signed ai) 12))).
  assert (S0 : RiscvSemantics.step segs (mkst regs (qpc 0) mem rom) = MachineOk (mkst r1 (qpc 1) mem rom)).
  { rewrite (step_auipc segs regs (qpc 0) mem rom w0 rP ai F0 E0 D0). nz_if. rewrite qpc_succ. reflexivity. }
  (* [comment removed for export] *)
  set (r2 := regupd r1 rP P).
  assert (S1 : RiscvSemantics.step segs (mkst r1 (qpc 1) mem rom) = MachineOk (mkst r2 (qpc 2) mem rom)).
  { rewrite (step_ld segs r1 (qpc 1) mem rom w1 rP rP im1 bsG P F1 E1 D1).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r1. gsimp. exact HG.
    - exact HGv. }
  (* [comment removed for export] *)
  set (r3 := regupd r2 rA (v_add b (Z_to_bv 64 n))).
  assert (S2 : RiscvSemantics.step segs (mkst r2 (qpc 2) mem rom) = MachineOk (mkst r3 (qpc 3) mem rom)).
  { rewrite (step_add segs r2 (qpc 2) mem rom w2 rA rB rS F2 E2 D2). nz_if. rewrite qpc_succ.
    unfold r3, r2, r1. gsimp. rewrite HB, HS. reflexivity. }
  (* [comment removed for export] *)
  set (r4 := regupd r3 rY sh).
  assert (S3 : RiscvSemantics.step segs (mkst r3 (qpc 3) mem rom) = MachineOk (mkst r4 (qpc 4) mem rom)).
  { rewrite (step_ld segs r3 (qpc 3) mem rom w3 rY rP (Z_to_bv 12 0) bsP sh F3 E3 D3).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r3, r2. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HP.
    - exact HPv. }
  (* [comment removed for export] *)
  set (r5 := regupd r4 rP (v_srli b 3)).
  assert (S4 : RiscvSemantics.step segs (mkst r4 (qpc 4) mem rom) = MachineOk (mkst r5 (qpc 5) mem rom)).
  { rewrite (step_srli segs r4 (qpc 4) mem rom w4 rP rB (Z_to_bv 6 3) F4 E4 D4). nz_if. rewrite qpc_succ.
    unfold r5, r4, r3, r2, r1. gsimp. rewrite HB. reflexivity. }
  (* [comment removed for export] *)
  set (r6 := regupd r5 rA (qlast b n)).
  assert (S5 : RiscvSemantics.step segs (mkst r5 (qpc 5) mem rom) = MachineOk (mkst r6 (qpc 6) mem rom)).
  { rewrite (step_addi segs r5 (qpc 5) mem rom w5 rA rA (Z_to_bv 12 (-1)) F5 E5 D5). nz_if. rewrite qpc_succ.
    unfold r6, r5, r4, r3. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r7 := regupd r6 rZ (v_srli (qlast b n) 3)).
  assert (S6 : RiscvSemantics.step segs (mkst r6 (qpc 6) mem rom) = MachineOk (mkst r7 (qpc 7) mem rom)).
  { rewrite (step_srli segs r6 (qpc 6) mem rom w6 rZ rA (Z_to_bv 6 3) F6 E6 D6). nz_if. rewrite qpc_succ.
    unfold r7, r6. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r8 := regupd r7 rP (qX sh b)).
  assert (S7 : RiscvSemantics.step segs (mkst r7 (qpc 7) mem rom) = MachineOk (mkst r8 (qpc 8) mem rom)).
  { rewrite (step_add segs r7 (qpc 7) mem rom w7 rP rY rP F7 E7 D7). nz_if. rewrite qpc_succ.
    unfold r8, r7, r6, r5, r4. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r9 := regupd r8 rY (qY sh b n)).
  assert (S8 : RiscvSemantics.step segs (mkst r8 (qpc 8) mem rom) = MachineOk (mkst r9 (qpc 9) mem rom)).
  { rewrite (step_add segs r8 (qpc 8) mem rom w8 rY rY rZ F8 E8 D8). nz_if. rewrite qpc_succ.
    unfold r9, r8, r7, r6, r5, r4. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r10 := regupd r9 rZ (qw1 sh b)).
  assert (S9 : RiscvSemantics.step segs (mkst r9 (qpc 9) mem rom) = MachineOk (mkst r10 (qpc 10) mem rom)).
  { rewrite (step_andi segs r9 (qpc 9) mem rom w9 rZ rP (Z_to_bv 12 (-8)) F9 E9 D9). nz_if. rewrite qpc_succ.
    unfold r10, r9, r8. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r11 := regupd r10 rW (qw2 sh b n)).
  assert (S10 : RiscvSemantics.step segs (mkst r10 (qpc 10) mem rom) = MachineOk (mkst r11 (qpc 11) mem rom)).
  { rewrite (step_andi segs r10 (qpc 10) mem rom w10 rW rY (Z_to_bv 12 (-8)) F10 E10 D10). nz_if. rewrite qpc_succ.
    unfold r11, r10, r9. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r12 := regupd r11 rZ (Z_to_bv 64 0)).
  assert (S11 : RiscvSemantics.step segs (mkst r11 (qpc 11) mem rom) = MachineOk (mkst r12 (qpc 12) mem rom)).
  { rewrite (step_ld segs r11 (qpc 11) mem rom w11 rZ rZ (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F11 E11 D11).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r11, r10. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW1.
    - reflexivity. }
  (* [comment removed for export] *)
  set (r13 := regupd r12 rW (Z_to_bv 64 0)).
  assert (S12 : RiscvSemantics.step segs (mkst r12 (qpc 12) mem rom) = MachineOk (mkst r13 (qpc 13) mem rom)).
  { rewrite (step_ld segs r12 (qpc 12) mem rom w12 rW rW (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F12 E12 D12).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r12, r11. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW2.
    - reflexivity. }
  (* [comment removed for export] *)
  set (r14 := regupd r13 rZ (Z_to_bv 64 0)).
  assert (S13 : RiscvSemantics.step segs (mkst r13 (qpc 13) mem rom) = MachineOk (mkst r14 (qpc 14) mem rom)).
  { rewrite (step_or segs r13 (qpc 13) mem rom w13 rZ rW rZ F13 E13 D13). nz_if. rewrite qpc_succ.
    unfold r14, r13, r12. gsimp. reflexivity. }
  (* [comment removed for export] *)
  assert (Hz : getr r14 rZ = Z_to_bv 64 0) by (unfold r14; gsimp; reflexivity).
  assert (Hz0 : getr r14 (Z_to_bv 5 0) = Z_to_bv 64 0) by reflexivity.
  assert (S14 : RiscvSemantics.step segs (mkst r14 (qpc 14) mem rom) = MachineOk (mkst r14 qok mem rom)).
  { unfold qok. destruct beq.
    - rewrite (step_beq_tk segs r14 (qpc 14) mem rom w14 rZ (Z_to_bv 5 0) bim F14 E14 D14); [reflexivity|].
      rewrite Hz, Hz0. reflexivity.
    - rewrite (step_bne_ft segs r14 (qpc 14) mem rom w14 rZ (Z_to_bv 5 0) bim F14 E14 D14); [rewrite qpc_succ; reflexivity|].
      rewrite Hz, Hz0. reflexivity. }
  exists r14. split.
  - repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - unfold r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1.
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    intros r H1 H2 H3 H4 H5. gsimp. reflexivity.
Qed.
End QC.

(* [comment removed for export] *)
Section QC2.
Context {fx : FPState}.
Variable segs : list Segment.
Variables (pc0 : Z) (rP rA rB rY rZ rW : reg) (ord : bool) (bim : bv 13) (beq : bool).
Hypothesis Hnz : rP <> 0%bv /\ rA <> 0%bv /\ rY <> 0%bv /\ rZ <> 0%bv /\ rW <> 0%bv.
Hypothesis Hd1 : rA <> rP /\ rY <> rP /\ rY <> rA /\ rZ <> rP /\ rZ <> rA /\ rZ <> rY /\ rW <> rP /\ rW <> rA /\ rW <> rY /\ rW <> rZ.
Hypothesis Hd2 : rB <> rP /\ rB <> rA /\ rB <> rY.
Hypothesis I0 : qins segs pc0 0 (Load SZ8 true rY rP (Z_to_bv 12 0)).
Hypothesis I1 : qins segs pc0 1 (if ord then ShiftImm ALU_SRL rP rB (Z_to_bv 6 3) else OpImm ALU_ADD rA rA (Z_to_bv 12 (-1))).
Hypothesis I2 : qins segs pc0 2 (if ord then OpImm ALU_ADD rA rA (Z_to_bv 12 (-1)) else ShiftImm ALU_SRL rP rB (Z_to_bv 6 3)).
Hypothesis I3 : qins segs pc0 3 (ShiftImm ALU_SRL rZ rA (Z_to_bv 6 3)).
Hypothesis I4 : qins segs pc0 4 (Op ALU_ADD rP rY rP).
Hypothesis I5 : qins segs pc0 5 (Op ALU_ADD rY rY rZ).
Hypothesis I6 : qins segs pc0 6 (OpImm ALU_AND rZ rP (Z_to_bv 12 (-8))).
Hypothesis I7 : qins segs pc0 7 (OpImm ALU_AND rW rY (Z_to_bv 12 (-8))).
Hypothesis I8 : qins segs pc0 8 (Load SZ8 true rZ rZ (Z_to_bv 12 0)).
Hypothesis I9 : qins segs pc0 9 (Load SZ8 true rW rW (Z_to_bv 12 0)).
Hypothesis I10 : qins segs pc0 10 (Op ALU_OR rZ rW rZ).
Hypothesis I11 : qins segs pc0 11 (Branch (if beq then BC_EQ else BC_NE) rZ (Z_to_bv 5 0) bim).

Definition qok2 : word := if beq then btgt (qpc pc0 11) (bv_signed bim) else qpc pc0 12.

#[using="ord Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11"] Theorem qc2_isteps : forall regs mem rom (b : word) (n : Z) (P sh : word) bsP,
  getr regs rB = b -> getr regs rP = P -> getr regs rA = v_add b (Z_to_bv 64 n) ->
  rdn segs mem P 8 = Some bsP -> bytes_le_to_Z bsP = bv_unsigned sh ->
  rdn segs mem (qw1 sh b) 8 = Some zeros8 -> rdn segs mem (qw2 sh b n) 8 = Some zeros8 ->
  exists regs',
    FxStep.isteps segs (mkst regs (qpc pc0 0) mem rom) (mkst regs' qok2 mem rom) /\
    getr regs' rP = qX sh b /\ getr regs' rY = qY sh b n /\ getr regs' rA = qlast b n /\
    getr regs' rZ = Z_to_bv 64 0 /\ getr regs' rW = Z_to_bv 64 0 /\
    (forall r, r <> rP -> r <> rA -> r <> rY -> r <> rZ -> r <> rW -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (ord Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom b n P sh bsP HB HPr HA HP HPv HW1 HW2.
  destruct Hnz as (NP & NA & NY & NZ & NW).
  destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
  destruct Hd2 as (DBP & DBA & DBY).
  destruct I0 as (w0 & F0 & E0 & D0). destruct I1 as (w1 & F1 & E1 & D1). destruct I2 as (w2 & F2 & E2 & D2).
  destruct I3 as (w3 & F3 & E3 & D3). destruct I4 as (w4 & F4 & E4 & D4). destruct I5 as (w5 & F5 & E5 & D5).
  destruct I6 as (w6 & F6 & E6 & D6). destruct I7 as (w7 & F7 & E7 & D7). destruct I8 as (w8 & F8 & E8 & D8).
  destruct I9 as (w9 & F9 & E9 & D9). destruct I10 as (w10 & F10 & E10 & D10). destruct I11 as (w11 & F11 & E11 & D11).
  (* [comment removed for export] *)
  set (r1 := regupd regs rY sh).
  assert (S0 : RiscvSemantics.step segs (mkst regs (qpc pc0 0) mem rom) = MachineOk (mkst r1 (qpc pc0 1) mem rom)).
  { rewrite (step_ld segs regs (qpc pc0 0) mem rom w0 rY rP (Z_to_bv 12 0) bsP sh F0 E0 D0).
    - nz_if. rewrite qpc_succ. reflexivity.
    - rewrite HPr. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HP.
    - exact HPv. }
  (* [comment removed for export] *)
  assert (S12 : exists r3, FxStep.isteps segs (mkst r1 (qpc pc0 1) mem rom) (mkst r3 (qpc pc0 3) mem rom) /\
            getr r3 rP = v_srli b 3 /\ getr r3 rA = qlast b n /\ (forall r, r <> rP -> r <> rA -> getr r3 r = getr r1 r)).
  { destruct ord.
    - set (ra1 := regupd r1 rP (v_srli b 3)). set (ra2 := regupd ra1 rA (qlast b n)).
      assert (Sa : RiscvSemantics.step segs (mkst r1 (qpc pc0 1) mem rom) = MachineOk (mkst ra1 (qpc pc0 2) mem rom)).
      { rewrite (step_srli segs r1 (qpc pc0 1) mem rom w1 rP rB (Z_to_bv 6 3) F1 E1 D1). nz_if. rewrite qpc_succ.
        unfold ra1, r1. gsimp. rewrite HB. reflexivity. }
      assert (Sb : RiscvSemantics.step segs (mkst ra1 (qpc pc0 2) mem rom) = MachineOk (mkst ra2 (qpc pc0 3) mem rom)).
      { rewrite (step_addi segs ra1 (qpc pc0 2) mem rom w2 rA rA (Z_to_bv 12 (-1)) F2 E2 D2). nz_if. rewrite qpc_succ.
        unfold ra2, ra1, r1. gsimp. rewrite HA. reflexivity. }
      exists ra2. split; [eapply FxStep.ist_step; [reflexivity | exact Sa|]; eapply FxStep.ist_step; [reflexivity | exact Sb|]; apply FxStep.ist_refl|].
      unfold ra2, ra1. split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. intros r H1 H2. gsimp. reflexivity.
    - set (ra1 := regupd r1 rA (qlast b n)). set (ra2 := regupd ra1 rP (v_srli b 3)).
      assert (Sa : RiscvSemantics.step segs (mkst r1 (qpc pc0 1) mem rom) = MachineOk (mkst ra1 (qpc pc0 2) mem rom)).
      { rewrite (step_addi segs r1 (qpc pc0 1) mem rom w1 rA rA (Z_to_bv 12 (-1)) F1 E1 D1). nz_if. rewrite qpc_succ.
        unfold ra1, r1. gsimp. rewrite HA. reflexivity. }
      assert (Sb : RiscvSemantics.step segs (mkst ra1 (qpc pc0 2) mem rom) = MachineOk (mkst ra2 (qpc pc0 3) mem rom)).
      { rewrite (step_srli segs ra1 (qpc pc0 2) mem rom w2 rP rB (Z_to_bv 6 3) F2 E2 D2). nz_if. rewrite qpc_succ.
        unfold ra2, ra1, r1. gsimp. rewrite HB. reflexivity. }
      exists ra2. split; [eapply FxStep.ist_step; [reflexivity | exact Sa|]; eapply FxStep.ist_step; [reflexivity | exact Sb|]; apply FxStep.ist_refl|].
      unfold ra2, ra1. split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. intros r H1 H2. gsimp. reflexivity. }
  destruct S12 as (r3 & Hs12 & G3P & G3A & G3o).
  assert (G3Y : getr r3 rY = sh) by (rewrite G3o by neq; unfold r1; gsimp; reflexivity).
  (* [comment removed for export] *)
  set (r4 := regupd r3 rZ (v_srli (qlast b n) 3)).
  assert (S3 : RiscvSemantics.step segs (mkst r3 (qpc pc0 3) mem rom) = MachineOk (mkst r4 (qpc pc0 4) mem rom)).
  { rewrite (step_srli segs r3 (qpc pc0 3) mem rom w3 rZ rA (Z_to_bv 6 3) F3 E3 D3). nz_if. rewrite qpc_succ. rewrite G3A. reflexivity. }
  (* [comment removed for export] *)
  set (r5 := regupd r4 rP (qX sh b)).
  assert (S4 : RiscvSemantics.step segs (mkst r4 (qpc pc0 4) mem rom) = MachineOk (mkst r5 (qpc pc0 5) mem rom)).
  { rewrite (step_add segs r4 (qpc pc0 4) mem rom w4 rP rY rP F4 E4 D4). nz_if. rewrite qpc_succ.
    unfold r5, r4. gsimp. rewrite G3Y, G3P. reflexivity. }
  set (r6 := regupd r5 rY (qY sh b n)).
  assert (S5 : RiscvSemantics.step segs (mkst r5 (qpc pc0 5) mem rom) = MachineOk (mkst r6 (qpc pc0 6) mem rom)).
  { rewrite (step_add segs r5 (qpc pc0 5) mem rom w5 rY rY rZ F5 E5 D5). nz_if. rewrite qpc_succ.
    unfold r6, r5, r4. gsimp. rewrite G3Y. reflexivity. }
  (* [comment removed for export] *)
  set (r7 := regupd r6 rZ (qw1 sh b)).
  assert (S6 : RiscvSemantics.step segs (mkst r6 (qpc pc0 6) mem rom) = MachineOk (mkst r7 (qpc pc0 7) mem rom)).
  { rewrite (step_andi segs r6 (qpc pc0 6) mem rom w6 rZ rP (Z_to_bv 12 (-8)) F6 E6 D6). nz_if. rewrite qpc_succ.
    unfold r7, r6, r5. gsimp. reflexivity. }
  set (r8 := regupd r7 rW (qw2 sh b n)).
  assert (S7 : RiscvSemantics.step segs (mkst r7 (qpc pc0 7) mem rom) = MachineOk (mkst r8 (qpc pc0 8) mem rom)).
  { rewrite (step_andi segs r7 (qpc pc0 7) mem rom w7 rW rY (Z_to_bv 12 (-8)) F7 E7 D7). nz_if. rewrite qpc_succ.
    unfold r8, r7, r6. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r9 := regupd r8 rZ (Z_to_bv 64 0)).
  assert (S8 : RiscvSemantics.step segs (mkst r8 (qpc pc0 8) mem rom) = MachineOk (mkst r9 (qpc pc0 9) mem rom)).
  { rewrite (step_ld segs r8 (qpc pc0 8) mem rom w8 rZ rZ (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F8 E8 D8).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r8, r7. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW1.
    - reflexivity. }
  set (r10 := regupd r9 rW (Z_to_bv 64 0)).
  assert (S9 : RiscvSemantics.step segs (mkst r9 (qpc pc0 9) mem rom) = MachineOk (mkst r10 (qpc pc0 10) mem rom)).
  { rewrite (step_ld segs r9 (qpc pc0 9) mem rom w9 rW rW (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F9 E9 D9).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r9, r8. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW2.
    - reflexivity. }
  (* [comment removed for export] *)
  set (r11 := regupd r10 rZ (Z_to_bv 64 0)).
  assert (S10 : RiscvSemantics.step segs (mkst r10 (qpc pc0 10) mem rom) = MachineOk (mkst r11 (qpc pc0 11) mem rom)).
  { rewrite (step_or segs r10 (qpc pc0 10) mem rom w10 rZ rW rZ F10 E10 D10). nz_if. rewrite qpc_succ.
    unfold r11, r10, r9. gsimp. reflexivity. }
  assert (Hz : getr r11 rZ = Z_to_bv 64 0) by (unfold r11; gsimp; reflexivity).
  assert (Hz0 : getr r11 (Z_to_bv 5 0) = Z_to_bv 64 0) by reflexivity.
  assert (S11 : RiscvSemantics.step segs (mkst r11 (qpc pc0 11) mem rom) = MachineOk (mkst r11 qok2 mem rom)).
  { unfold qok2. destruct beq.
    - rewrite (step_beq_tk segs r11 (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [reflexivity|].
      rewrite Hz, Hz0. reflexivity.
    - rewrite (step_bne_ft segs r11 (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [rewrite qpc_succ; reflexivity|].
      rewrite Hz, Hz0. reflexivity. }
  exists r11. split.
  - eapply FxStep.ist_step; [reflexivity | exact S0|]. eapply FxStep.isteps_trans; [exact Hs12|].
    repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - unfold r11, r10, r9, r8, r7, r6, r5, r4.
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. split; [gsimp; exact G3A|].
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    intros r H1 H2 H3 H4 H5. gsimp. rewrite (G3o r H1 H2). unfold r1. gsimp. reflexivity.
Qed.
End QC2.
(* [comment removed for export] *)
End FxQChk.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record loopspec : Type := LS {
  ls_inv : sst;                 (* [comment removed for export] *)
  ls_meas : lin;                (* [comment removed for export] *)
  ls_params : list positive;    (* [comment removed for export] *)
  ls_fuel : nat;                (* [comment removed for export] *)
  ls_stops : list Z             (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition meas_dec (L : sst) (σ : tree lin) (m : lin) : bool :=
  match lin_off (lsubst σ m) m with
  | Some d =>
      let d' := sgn64 d in
      if Z.ltb d' 0 then let '(lo, _) := irange (s_facts L) m in Z.leb (- d') lo else false
  | None => false
  end.
Definition params_fixed (σ : tree lin) (ps : list positive) : bool := forallb (fun x => lin_eqb (svar σ x) (lvar x)) ps.
Definition back_ok (P : sst) (m : lin) (ps : list positive) (L : sst) : bool :=
  let σ := match_st L P in (entails L P σ && params_fixed σ ps && meas_dec L σ m)%bool.

Definition loop_leaves (t : tree xi) (img : tree Z) (ls : loopspec) : list sst :=
  fx_explore t img (ls_fuel ls) (s_pc (ls_inv ls) :: ls_stops ls) (ls_inv ls) [].

Definition loop_check (t : tree xi) (img : tree Z) (ls : loopspec) : option (list sst) :=
  let P := ls_inv ls in
  if (state_wf P && lwf (s_next P) (ls_meas ls) && forallb (fun x => Pos.ltb x (s_next P)) (ls_params ls))%bool then
    let leaves := loop_leaves t img ls in
    if forallb (fun L => if Z.eqb (s_pc L) (s_pc P) then back_ok P (ls_meas ls) (ls_params ls) L else true) leaves
    then Some (List.filter (fun L => negb (Z.eqb (s_pc L) (s_pc P))) leaves) else None
  else None.

Lemma meas_dec_sound : forall E L σ m, Forall (fact_ok E) (s_facts L) -> meas_dec L σ m = true ->
  bv_unsigned (lden E (lsubst σ m)) < bv_unsigned (lden E m).
Proof.
  intros E L σ m HF H. unfold meas_dec in H.
  destruct (lin_off (lsubst σ m) m) as [d|] eqn:Hoff; [|discriminate].
  destruct (Z.ltb (sgn64 d) 0) eqn:Hneg; [|discriminate]. apply Z.ltb_lt in Hneg.
  pose proof (irange_sound E _ m HF) as Hlo. destruct (irange (s_facts L) m) as [lo hi]. cbn [fst snd] in Hlo. apply Z.leb_le in H.
  destruct (lin_off_sound E _ _ _ Hoff) as [Hv Hd]. rewrite lden_lsub in Hv.
  pose proof (f_equal bv_unsigned Hv) as Hu. rewrite bv_sub_unsigned, u_small64 in Hu by exact Hd.
  unfold bv_wrap, bv_modulus in Hu. change (2 ^ Z.of_N 64) with two64 in Hu.
  pose proof (u_range E m) as R1. pose proof (u_range E (lsubst σ m)) as R2.
  assert (Hm : eqm (bv_unsigned (lden E (lsubst σ m))) (bv_unsigned (lden E m) + sgn64 d)).
  { eapply eqm_trans; [|apply eqm_add; [apply eqm_refl | apply eqm_sym, sgn64_eqm; exact Hd]].
    unfold eqm. rewrite <- Hu. rewrite Z.add_mod_idemp_r by (unfold two64; lia).
    replace (bv_unsigned (lden E m) + (bv_unsigned (lden E (lsubst σ m)) - bv_unsigned (lden E m))) with (bv_unsigned (lden E (lsubst σ m))) by lia.
    reflexivity. }
  unfold eqm in Hm. rewrite (Z.mod_small (bv_unsigned (lden E (lsubst σ m)))) in Hm by exact R2.
  rewrite (Z.mod_small (bv_unsigned (lden E m) + sgn64 d)) in Hm by lia. lia.
Qed.

Lemma params_fixed_sound : forall E σ ps x, params_fixed σ ps = true -> In x ps -> ecomp E σ x = E x.
Proof.
  intros E σ ps x H Hx. unfold params_fixed in H. rewrite forallb_forall in H. pose proof (H x Hx) as Hl.
  apply lin_eqb_eq in Hl. unfold ecomp. rewrite Hl. apply lden_lvar.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Theorem loop_sound_fp : forall t img ls exits, tbl_ok segs t -> img_ok segs img -> loop_check t img ls = Some exits ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L exits /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls exits Ht Himg Hck. unfold loop_check in Hck.
  set (P := ls_inv ls) in *. set (m := ls_meas ls) in *.
  destruct (state_wf P && lwf (s_next P) m && forallb (fun x => Pos.ltb x (s_next P)) (ls_params ls))%bool eqn:Hw; [|discriminate].
  apply andb_prop in Hw as [Hw Hps]. apply andb_prop in Hw as [HwP Hwm]. rewrite forallb_forall in Hps.
  destruct (forallb (fun L => if Z.eqb (s_pc L) (s_pc P) then back_ok P m (ls_params ls) L else true) (loop_leaves t img ls)) eqn:Hall;
    [|discriminate].
  injection Hck as <-. rewrite forallb_forall in Hall.
  (* [comment removed for export] *)
  assert (Hind : forall n, forall E ms, Z.to_nat (bv_unsigned (lden E m)) = n -> sden segs E P ms ->
            exists L ms' E', In L (List.filter (fun L => negb (Z.eqb (s_pc L) (s_pc P))) (loop_leaves t img ls)) /\
                             isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x) /\ fpc t ms ms').
  { intros n. induction n as [n IH] using (well_founded_induction lt_wf). intros E ms Hn Hden.
    destruct (explore_sound_fp segs t img (ls_fuel ls) (s_pc P :: ls_stops ls) P [] E ms Ht Himg Hden) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfp1).
    assert (Hpar : forall x, In x (ls_params ls) -> E1 x = E x) by (intros x Hx; symmetry; apply Ha1; apply Pos.ltb_lt, Hps, Hx).
    pose proof (Hall L HL) as HLok.
    destruct (Z.eqb (s_pc L) (s_pc P)) eqn:Hpc.
    - (* [comment removed for export] *)
      unfold back_ok in HLok. set (σ := match_st L P) in HLok.
      apply andb_prop in HLok as [HLok Hdec]. apply andb_prop in HLok as [Hent Hfix].
      pose proof (sden_0 _ _ _ _ Hd1) as Hd10.
      pose proof (entails_sden segs E1 L P σ ms1 Hd10 Hent HwP) as HdP.
      destruct Hd10 as (_ & _ & _ & _ & _ & _ & HF1 & _).
      pose proof (meas_dec_sound E1 L σ m HF1 Hdec) as Hlt. rewrite lden_lsubst in Hlt.
      rewrite (lden_agree (s_next P) E1 E m Hwm (fun x Hx => eq_sym (Ha1 x Hx))) in Hlt.
      destruct (IH (Z.to_nat (bv_unsigned (lden (ecomp E1 σ) m))) ltac:(pose proof (u_range (ecomp E1 σ) m); lia) (ecomp E1 σ) ms1 eq_refl HdP)
        as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hpar2 & Hfp2).
      exists L2, ms2, E2. split; [exact HL2|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
      split; [|exact (fpc_trans _ _ _ _ Hfp1 Hfp2)].
      intros x Hx. rewrite (Hpar2 x Hx). rewrite (params_fixed_sound E1 σ _ x Hfix Hx). apply Hpar. exact Hx.
    - (* [comment removed for export] *)
      exists L, ms1, E1. split; [apply (proj2 (filter_In _ _ _)); split; [exact HL | rewrite Hpc; reflexivity]|].
      split; [exact Hst1|]. split; [exact Hd1 | split; [exact Hpar | exact Hfp1]]. }
  intros E ms Hden. exact (Hind _ E ms eq_refl Hden).
Qed.
#[using="Type"] Theorem loop_sound : forall t img ls exits, tbl_ok segs t -> img_ok segs img -> loop_check t img ls = Some exits ->
  forall E ms, sden segs E (ls_inv ls) ms ->
  exists L ms' E', In L exits /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x (ls_params ls) -> E' x = E x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ls exits Ht Himg Hck E ms Hd.
  destruct (loop_sound_fp t img ls exits Ht Himg Hck E ms Hd) as (L & ms' & E' & H1 & H2 & H3 & H4 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

End WithSegs.
