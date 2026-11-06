(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_SR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run I2Inv I2NodeLib I2NodeMem
  I2NodeM I2NodeR I2NodeA I2NodeF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

Section Sound.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Variable IMX : fimage.
  Variable K : i2consts.
  Variable code : itrie finstr.
  Let IM := im_ro IMX.
  Let RO := ro_of K.
  Hypothesis HK : K_ok K = true.
  Hypothesis HHx : heap_sr_hyps_x H.
  Hypothesis HIMX : image_ok rsegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Hypothesis Hcode : code_ok rsegs code.
  Hypothesis HROC : ro_const H K.
  Let HH : heap_sr_hyps H := proj1 HHx.

  Lemma Hnw : im_nowr IM.
  Proof. intros a sg Hf. exact (im_ro_find_seg IMX a sg Hf). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cells0x (M : itrie region) (pn ci : int) : Prop := cellx M 0%uint63 pn ci.

  Lemma cells0_in_of : forall M M',
    (forall pn ci, cells0x M pn ci -> cells0x M' pn ci) -> cells0_in K M' -> cells0_in K M.
  Proof.
    intros M M' Hmono Hin rg0 pn p ci c H0 Hp Hc.
    destruct (Hmono pn ci ltac:(exists rg0, p, c; repeat split; assumption)) as (rg0' & p' & c' & H0' & Hp' & Hc').
    exact (Hin rg0' pn p' ci c' H0' Hp' Hc').
  Qed.

  Lemma cells0x_run : forall bp k F F' r cnt pn ci,
    fx_run IM code RO bp k F = (F', r, cnt) -> cells0x (f_mem F) pn ci -> cells0x (f_mem F') pn ci.
  Proof. intros. eapply fx_run_cellx; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma cells0x_set_errno : forall te M M2 pn ci,
    set_errno K te M = Some M2 -> cells0x M pn ci -> cells0x M2 pn ci.
  Proof.
    intros te M M2 pn ci Hs (rg0 & p & c & H0 & Hp & Hc).
    destruct (set_errno_inv _ _ _ _ Hs) as (rg0' & pe & H0' & Hpe & _ & ->). rewrite H0 in H0'. injection H0' as <-.
    unfold cells0x, cellx. exists (err_region K te rg0 pe). unfold err_region. cbn [rg_pages].
    destruct (pn =? (c_errcell K >> 12))%uint63 eqn:Epn.
    - apply Uint63.eqb_spec in Epn. subst pn. rewrite Hpe in Hp. injection Hp as <-.
      eexists. destruct (ci =? ((c_errcell K land 4095) >> 3))%uint63 eqn:Eci.
      + eexists. split; [apply iget_iset_same|]. split; [apply iget_iset_same|]. cbn [pg_cells]. rewrite iget_iset, Eci. reflexivity.
      + exists c. split; [apply iget_iset_same|]. split; [apply iget_iset_same|]. cbn [pg_cells]. rewrite iget_iset, Eci. exact Hc.
    - exists p, c. split; [apply iget_iset_same|]. split; [rewrite iget_iset, Epn; exact Hp | exact Hc].
  Qed.

  Lemma cells0x_drop_stack : forall off M M1 pn ci,
    drop_stack off M = Some M1 -> cells0x M pn ci -> cells0x M1 pn ci.
  Proof.
    intros off M M1 pn ci Hd (rg0 & p & c & H0 & Hp & Hc).
    destruct (drop_stack_inv _ _ _ Hd) as (rg1 & H1 & ->).
    exists rg0, p, c. rewrite iget_iset. change ((0 =? 1)%uint63) with false. repeat split; assumption.
  Qed.

  Lemma cells0x_iset_other : forall t rg M pn ci, t <> 0%uint63 -> cells0x M pn ci -> cells0x (iset t rg M) pn ci.
  Proof.
    intros t rg M pn ci Ht (rg0 & p & c & H0 & Hp & Hc). exists rg0, p, c. rewrite iget_iset.
    rewrite (eqb_neq_false 0%uint63 t) by (intros E; apply Ht; symmetry; exact E). repeat split; assumption.
  Qed.

  Lemma cells0x_iremove_other : forall t M pn ci, t <> 0%uint63 -> cells0x M pn ci -> cells0x (iremove t M) pn ci.
  Proof.
    intros t M pn ci Ht (rg0 & p & c & H0 & Hp & Hc). exists rg0, p, c. rewrite iget_iremove.
    rewrite (eqb_neq_false 0%uint63 t) by (intros E; apply Ht; symmetry; exact E). repeat split; assumption.
  Qed.

  Lemma i_n_ne0 : forall st off l, call_ok K st = Some (off, l) -> i_n st <> 0%uint63.
  Proof.
    intros st off l Hc E. destruct (call_ok_inv _ _ _ _ Hc) as (_ & _ & _ & _ & _ & _ & H2).
    rewrite E in H2. change (to_Z 0%uint63) with 0 in H2. slia.
  Qed.

  Lemma cells0x_node_at : forall st st' pn ci,
    node_at K st = Some st' -> cells0x (f_mem (i_F st)) pn ci -> cells0x (f_mem (i_F st')) pn ci.
  Proof.
    intros st st' pn ci Hn Hc. unfold node_at in Hn.
    destruct (f_pc (i_F st) =? 0)%uint63; [discriminate|].
    destruct (f_pc (i_F st) =? c_malloc K)%uint63.
    { unfold node_malloc in Hn. destruct (call_ok K st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (conc63 (FxState.rget (i_F st) 10)) as [n|]; [|discriminate].
      match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
      destruct (drop_stack off (f_mem (i_F st))) as [M1|] eqn:HM1; [|discriminate].
      destruct (set_errno K (i_n st + 15)%uint63 (iset (i_n st) (blk_region n 4 iempty) M1)) as [M2|] eqn:HM2; [|discriminate].
      injection Hn as <-. cbn [i_F f_mem].
      eapply cells0x_set_errno; [exact HM2|]. apply cells0x_iset_other; [exact (i_n_ne0 _ _ _ Hco)|].
      eapply cells0x_drop_stack; [exact HM1 | exact Hc]. }
    destruct (f_pc (i_F st) =? c_free K)%uint63.
    { destruct (conc63 (FxState.rget (i_F st) 10)).
      - unfold node_free_null in Hn. destruct (call_link (i_F st)); [|discriminate].
        destruct (conc63 (FxState.rget (i_F st) 10)); [|discriminate].
        match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
        injection Hn as <-. exact Hc.
      - unfold node_free in Hn. destruct (call_ok K st) as [[off l]|] eqn:Hco; [|discriminate].
        destruct (base_tag (FxState.rget (i_F st) 10)) as [tb|] eqn:Htb; [|discriminate].
        destruct (bsize_of tb (i_blk st)); [|discriminate]. destruct (iget tb (f_mem (i_F st))); [|discriminate].
        match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate] end.
        destruct (drop_stack off (iremove tb (f_mem (i_F st)))) as [M1|] eqn:HM1; [|discriminate].
        destruct (set_errno K (i_n st + 15)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
        injection Hn as <-. cbn [i_F f_mem].
        rewrite !andb_true_iff in Hg. destruct Hg as [_ Htb2]. apply Uint63.leb_spec in Htb2. change (to_Z 2%uint63) with 2 in Htb2.
        eapply cells0x_set_errno; [exact HM2|]. eapply cells0x_drop_stack; [exact HM1|].
        apply cells0x_iremove_other; [|exact Hc]. intros E. rewrite E in Htb2. change (to_Z 0%uint63) with 0 in Htb2. slia. }
    destruct (f_pc (i_F st) =? c_realloc K)%uint63.
    { unfold node_realloc in Hn. destruct (call_ok K st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (base_tag (FxState.rget (i_F st) 10)) as [tb|]; [|discriminate].
      destruct (conc63 (FxState.rget (i_F st) 11)) as [n'|]; [|discriminate].
      destruct (bsize_of tb (i_blk st)) as [n|]; [|discriminate]. destruct (iget tb (f_mem (i_F st))) as [rgb|]; [|discriminate].
      match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate] end.
      cbv zeta in Hn.
      match type of Hn with context [drop_stack off ?M] => destruct (drop_stack off M) as [M1|] eqn:HM1; [|discriminate] end.
      destruct (set_errno K (i_n st + 15)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
      injection Hn as <-. cbn [i_F f_mem].
      rewrite !andb_true_iff in Hg. destruct Hg as [[[[[[[[[[[_ _] Htb2] _] _] _] _] _] _] _] _] _].
      apply Uint63.leb_spec in Htb2. change (to_Z 2%uint63) with 2 in Htb2.
      eapply cells0x_set_errno; [exact HM2|]. eapply cells0x_drop_stack; [exact HM1|].
      apply cells0x_iset_other; [exact (i_n_ne0 _ _ _ Hco)|].
      apply cells0x_iremove_other; [|exact Hc]. intros E. rewrite E in Htb2. change (to_Z 0%uint63) with 0 in Htb2. slia. }
    destruct (f_pc (i_F st) =? c_aalloc K)%uint63; [|discriminate].
    unfold node_aalloc in Hn. destruct (call_ok K st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (conc63 (FxState.rget (i_F st) 10)) as [al|]; [|discriminate].
    destruct (conc63 (FxState.rget (i_F st) 11)) as [n|]; [|discriminate].
    destruct (log2_al al) as [lg|]; [|discriminate].
    match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
    destruct (drop_stack off (f_mem (i_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (set_errno K (i_n st + 15)%uint63 (iset (i_n st) (blk_region n lg iempty) M1)) as [M2|] eqn:HM2; [|discriminate].
    injection Hn as <-. cbn [i_F f_mem].
    eapply cells0x_set_errno; [exact HM2|]. apply cells0x_iset_other; [exact (i_n_ne0 _ _ _ Hco)|].
    eapply cells0x_drop_stack; [exact HM1 | exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma i2_run_step : forall fuel st,
    i2_run IM code K (S fuel) st =
    match fx_run IM code (ro_of K) no_bp 40 (i_F st) with
    | (F', r, _) =>
        let st' := with_F st F' in
        match r with
        | SStuck c =>
            if (c =? 1)%uint63 then bindn 10 st' (node_at K st') (i2_run IM code K fuel)
            else if (c =? 2)%uint63 then (if is_final K code F' then Done st' else Rej 2 st')
            else Rej (100 + c)%uint63 st'
        | SEcall => Rej 3 st'
        | SBreak => Rej 4 st'
        | SFuel => Rej 5 st'
        end
    end.
  Proof. intros. reflexivity. Qed.

  Lemma i2_run_0 : forall st, i2_run IM code K 0 st = Rej 90 st.
  Proof. intros. reflexivity. Qed.

  Lemma cells0x_i2_run : forall fuel st st' pn ci,
    i2_run IM code K fuel st = Done st' -> cells0x (f_mem (i_F st)) pn ci -> cells0x (f_mem (i_F st')) pn ci.
  Proof.
    induction fuel as [|fuel IH]; intros st st' pn ci Hr Hc; [rewrite i2_run_0 in Hr; discriminate|].
    rewrite i2_run_step in Hr.
    destruct (fx_run IM code (ro_of K) no_bp 40 (i_F st)) as [[F' r] cnt] eqn:Hrun. cbv zeta in Hr.
    pose proof (cells0x_run _ _ _ _ _ _ pn ci Hrun Hc) as Hc'.
    destruct r as [| | |c]; try discriminate.
    destruct (c =? 1)%uint63.
    - unfold bindn in Hr. destruct (node_at K (with_F st F')) as [st''|] eqn:Hn; [|discriminate].
      apply (IH st'' st' pn ci Hr). exact (cells0x_node_at _ _ pn ci Hn Hc').
    - destruct (c =? 2)%uint63; [|discriminate]. destruct (is_final K code F'); [|discriminate].
      injection Hr as <-. exact Hc'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem i2_run_sound : forall fuel Q st st' rho ms mo,
    i2_run IM code K fuel st = Done st' ->
    cells0_in K (f_mem (i_F st')) ->
    I2R H IMX K Q st rho ms mo ->
    hs_SR H (fun c' => exists rho', I2R H IMX K Q st' rho' (cfg_ms c') (cfg_model c') /\ is_final K code (i_F st') = true)
         (mkCfg ms mo).
  Proof.
    induction fuel as [|fuel IH]; intros Q st st' rho ms mo Hr Hc0 HI; [rewrite i2_run_0 in Hr; discriminate|].
    rewrite i2_run_step in Hr.
    destruct (fx_run IM code (ro_of K) no_bp 40 (i_F st)) as [[F' r] cnt] eqn:Hrun. cbv zeta in Hr.
    (* [comment removed for export] *)
    assert (Hc0' : cells0_in K (f_mem F')).
    { destruct r as [| | |c]; try discriminate.
      destruct (c =? 1)%uint63.
      - unfold bindn in Hr. destruct (node_at K (with_F st F')) as [st''|] eqn:Hn; [|discriminate].
        apply (cells0_in_of (f_mem F') (f_mem (i_F st'))); [|exact Hc0].
        intros pn ci Hc. apply (cells0x_i2_run _ _ _ pn ci Hr). exact (cells0x_node_at _ _ pn ci Hn Hc).
      - destruct (c =? 2)%uint63; [|discriminate]. destruct (is_final K code F'); [|discriminate].
        injection Hr as <-. exact Hc0. }
    eapply (sr_seq H HH).
    { exact (seg_sound H IMX K code Hcode HK HHx Hnw Q st rho ms mo F' r cnt Hrun HI Hc0'). }
    intros [ms1 mo1] [HI1 Hmo1]. cbn [cfg_ms cfg_model] in HI1, Hmo1. subst mo1.
    destruct r as [| | |c]; try discriminate.
    destruct (c =? 1)%uint63.
    - (* [comment removed for export] *)
      unfold bindn in Hr. destruct (node_at K (with_F st F')) as [st''|] eqn:Hn; [|discriminate].
      destruct (HK_pcs K HK) as (Emal & Efree & Erea & Eaal).
      assert (Hnode : hs_SR H (fun c' => exists rho', I2R H IMX K Q st'' rho' (cfg_ms c') (cfg_model c')) (mkCfg ms1 mo)).
      { unfold node_at in Hn. cbn [i_F with_F] in Hn.
        destruct (f_pc F' =? 0)%uint63 eqn:E0; [discriminate|].
        destruct (f_pc F' =? c_malloc K)%uint63 eqn:Em.
        { apply Uint63.eqb_spec in Em.
          apply (node_malloc_sound H IMX K HK HHx HIMX HWRX HROC Q (with_F st F') st'' rho ms1 mo Hn); [|exact Hc0' | exact HI1].
          cbn [i_F with_F]. rewrite Em, Emal. apply toZ_of_Z_small. unfold RMALLOC_SYM. slia. }
        destruct (f_pc F' =? c_free K)%uint63 eqn:Ef.
        { apply Uint63.eqb_spec in Ef.
          assert (Hpc : to_Z (f_pc (i_F (with_F st F'))) = RFREE_SYM).
          { cbn [i_F with_F]. rewrite Ef, Efree. apply toZ_of_Z_small. unfold RFREE_SYM. slia. }
          destruct (conc63 (FxState.rget F' 10)).
          - exact (node_free_null_sound H IMX K HHx Q (with_F st F') st'' rho ms1 mo Hn Hpc HI1).
          - exact (node_free_sound H IMX K HK HHx HIMX HWRX HROC Q (with_F st F') st'' rho ms1 mo Hn Hpc Hc0' HI1). }
        destruct (f_pc F' =? c_realloc K)%uint63 eqn:Er.
        { apply Uint63.eqb_spec in Er.
          apply (node_realloc_sound H IMX K HK HHx HIMX HWRX HROC Q (with_F st F') st'' rho ms1 mo Hn); [|exact Hc0' | exact HI1].
          cbn [i_F with_F]. rewrite Er. destruct Erea as [E | E]; rewrite E; [apply toZ_of_Z_small; unfold RREALLOC_SYM; slia|].
          exfalso. rewrite Er, E, Uint63.eqb_refl in E0. discriminate. }
        destruct (f_pc F' =? c_aalloc K)%uint63 eqn:Ea; [|discriminate].
        apply Uint63.eqb_spec in Ea.
        apply (node_aalloc_sound H IMX K HK HHx HIMX HWRX HROC Q (with_F st F') st'' rho ms1 mo Hn); [|exact Hc0' | exact HI1].
        cbn [i_F with_F]. rewrite Ea. destruct Eaal as [E | E]; rewrite E; [apply toZ_of_Z_small; unfold RAALLOC_SYM; slia|].
        exfalso. rewrite Ea, E, Uint63.eqb_refl in E0. discriminate. }
      eapply (sr_seq H HH); [exact Hnode|].
      intros [ms2 mo2] [rho2 HI2]. cbn [cfg_ms cfg_model] in HI2.
      exact (IH Q st'' st' rho2 ms2 mo2 Hr Hc0 HI2).
    - destruct (c =? 2)%uint63; [|discriminate]. destruct (is_final K code F') eqn:Hfin; [|discriminate].
      injection Hr as <-. apply (sr_done H HH). exists rho. split; [exact HI1 | exact Hfin].
  Qed.
End Sound.
