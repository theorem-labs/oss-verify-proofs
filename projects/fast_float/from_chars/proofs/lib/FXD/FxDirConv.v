(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChAdd FxChStart FxChain FxChDir.

Module FxOpenNF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChain FxChEnt FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv FxChDir.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition open_nf (fsm : Fs.Fs) (dirfd : word) (c : cstr_result) (e : Z) : Prop :=
  (dirfd = AT_FDCWD32 /\ exists p, c = CstrOk p /\ path_eqb p [] = false /\ path_has_slash p = false /\ path_is_dirref p = false /\
                                   fs_lookup fsm p = None /\ e = ENOENT) \/
  (c = CstrOk [] /\ e = ENOENT) \/ (c = CstrTooLong /\ e = ENAMETOOLONG).

Section NF.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.
Hypothesis Hfs : sc_fs cfg = true.

#[using="Hfs"] Theorem den_openat_nf : forall model0 E L M ms model (A : TSet) (c0 flags e : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 56 -> arg L 0 = Some c0 -> arg L 2 = Some flags -> Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) open_ignored_flags = 0 ->
  open_nf (m_fs model0) (fd32 (Z_to_bv 64 c0))
    (read_cstr (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r)))) e ->
  ranges_avoid (Hof E M model) [(lden E (rget (s_regs L) (rkey a1r)),
                                 cstr_access_len_aux (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r))) path_max)] ->
  (forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst (bv_unsigned (errno_ret e)))) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') A) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) A.
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros model0 E L M ms model A c0 flags e Hd H7 H0 H2 Hfl Hnf Hav HA.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17) in *.
  assert (Hx8 : x8 = Z_to_bv 64 56) by exact (a7_const segs E L (restrict H ms) ms 56 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 c0) by exact (gpr_const segs E L (restrict H ms) ms 0 c0 Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = lden E (rget (s_regs L) (rkey a1r))) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 2 flags Hsd eq_refl ltac:(lia) H2).
  set (i := sys_input segs ms1 x8) in *.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 c0) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg0).
  assert (A1 : in_arg i 1 = lden E (rget (s_regs L) (rkey a1r))) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg1).
  assert (A2 : in_arg i 2 = Z_to_bv 64 flags) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg2).
  assert (Hfm : m_fs model = m_fs model0) by (destruct Hvmo as (_ & _ & H3' & _); unfold m_fs; rewrite H3'; reflexivity).
  set (pl := lden E (rget (s_regs L) (rkey a1r))) in *.
  set (ci := [(pl, cstr_access_len_aux (in_mem i) pl path_max)]) in *.
  (* [comment removed for export] *)
  assert (Hspo : forall o, syscall_spec i model o <-> record_copyins ci (err_ret e) i model o).
  { intro o. rewrite (syscall_spec_56 i model o Hno). rewrite A0, A1, A2.
    destruct Hnf as [(Hdfd & p & Hc & Hne & Hsl & Hdr & Hlk & ->) | [(Hc & ->) | (Hc & ->)]].
    - rewrite (openat_rd_reduce (fd32 (Z_to_bv 64 c0)) pl (Z_to_bv 64 flags) p i model o Hdfd Hfl Hc Hne Hsl).
      fold ci. unfold openat_read_spec. rewrite Hdr, Hfm, Hlk. reflexivity.
    - exact (openat_empty_reduce (fd32 (Z_to_bv 64 c0)) pl (Z_to_bv 64 flags) i model o Hfl Hc).
    - exact (openat_toolong_reduce (fd32 (Z_to_bv 64 c0)) pl (Z_to_bv 64 flags) i model o Hfl Hc). }
  assert (Hw0 : forall z, lwf (s_next L) (lconst z) = true) by reflexivity.
  assert (HcA : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci (errno_ret e) ci))) m'') A).
  { intros m'' Hinv'' Hsb''. apply HA.
    pose proof (den_ret_ci0 segs LIMIT mem0 model0 E L M ms model (lconst (bv_unsigned (errno_ret e))) ci m'' Hd (Hw0 _) Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 unit
             (fun _ => ret_ci (errno_ret e) ci) (fun _ => model) (fun _ => []) (fun _ => A) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspo. apply record_copyins_ok_iff. exists (mkEffect (errno_ret e) [] []). split.
      2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
          rewrite app_nil_r. reflexivity. }
      apply err_ret_ok_iff. auto.
    + intros eff m' evs Hs. apply Hspo, record_copyins_ok_iff in Hs as (eff0 & Hs & ->).
      apply err_ret_ok_iff in Hs as (-> & -> & ->). exists tt. auto.
    + intros Hs. apply Hspo, record_copyins_unmodeled_iff in Hs. exact (err_ret_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_fs; [exact Hfs | exact Hno].
    + intros []. exact Hh.
    + intros []. apply lazy_cover_mkH_app; intros x Hx'; exact Hx'.
    + intros []. exact Hminv.
    + intros []. unfold ret_ci, syscall_effect_accesses; cbn [eff_copyins eff_writes write_accesses]; rewrite app_nil_r; exact Hav.
    + intros [] m'' Hinv'' Hsb''. exact (HcA m'' Hinv'' Hsb'').
  - apply (t_alt_const_nil unit tt A).
    exact (realizes_cfg_nonempty segs cfg _ _ (HcA model Hminv (same_but_materialized_refl _))).
Qed.
End NF.
End FxOpenNF.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint add_facts (S : sst) (fs : list fact) : sst :=
  match fs with [] => S | f :: r => add_facts (add_fact S f) r end.
Lemma add_facts_next : forall fs S, s_next (add_facts S fs) = s_next S.
Proof. induction fs as [|f r IH]; intros S; cbn [add_facts]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma add_facts_rgs : forall fs S, s_rgs (add_facts S fs) = s_rgs S.
Proof. induction fs as [|f r IH]; intros S; cbn [add_facts]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition conv_post (S : sst) (f : region -> bool) (fs : list fact) (pv sz : lin) (bs : list Z) : sst :=
  mat_post2 (add_facts (drop_post S f) fs) pv sz bs.

Lemma conv_post_next : forall S f fs pv sz bs, s_next (conv_post S f fs pv sz bs) = s_next S.
Proof. intros S f fs pv sz bs. unfold conv_post, mat_post2. cbn [s_next]. rewrite add_facts_next. reflexivity. Qed.

Section Conv.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma den_add_facts : forall fs E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  Forall (fun g => fwf (s_next S) g = true /\ fact_ok E g) fs -> DEN segs LIMIT model0 mem0 E (add_facts S fs) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs as [|g r IH]; intros E S M ms model Hd Hfs; cbn [add_facts]; [exact Hd|].
  inversion Hfs as [|? ? [Hw Hg] Hr]; subst.
  apply IH; [|exact Hr].
  apply den_addfact; [exact Hd|]. intros E' Ha. exact (fact_ok_agree _ E E' g Hw Ha Hg).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_rd1 : forall E m R i, rg_ok segs E m R -> 0 <= i < rsz E R ->
  rd1 segs m (Z_to_bv 64 (uE E (rg_base R) + i)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i (_ & _ & Hpts & _) Hi. specialize (Hpts i Hi). unfold uE.
  destruct (rg_kind R).
  all: first [ exact (proj1 Hpts) | exact (proj1 (proj1 Hpts)) | exact Hpts
             | (destruct Hpts as [H1 H2]; unfold rd1; rewrite H1; exact H2) ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_filter_R0 : forall E (f : region -> bool) rgs R0 w, rgs_disj E rgs -> In R0 rgs -> f R0 = true ->
  uE E (rg_base R0) <= w < uE E (rg_base R0) + rsz E R0 -> 0 <= w < two64 ->
  outside E (List.filter (fun R => negb (f R)) rgs) (Z_to_bv 64 w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E f rgs R0 w. induction rgs as [|R rs IH]; intros Hdj Hin Hf Hw Hw64; [destruct Hin|].
  cbn [rgs_disj] in Hdj. destruct Hdj as [HR Hrs].
  assert (Hu : bv_unsigned (Z_to_bv 64 w) = w) by exact (u64_small w Hw64).
  unfold outside. rewrite Forall_forall. intros R' HR'. apply filter_In in HR' as [HR' Hf'].
  rewrite Hu. unfold uE in Hw. rewrite Forall_forall in HR.
  destruct Hin as [<-|Hin].
  - destruct HR' as [<-|HR']; [rewrite Hf in Hf'; discriminate|].
    specialize (HR R' HR'). unfold rg_disj in HR. lia.
  - destruct HR' as [<-|HR'].
    + specialize (HR R0 Hin). unfold rg_disj in HR. lia.
    + specialize (IH Hrs Hin Hf Hw Hw64). unfold outside in IH. rewrite Forall_forall in IH.
      assert (Hk : In R' (List.filter (fun R => negb (f R)) rs)) by (apply filter_In; split; assumption).
      specialize (IH R' Hk). rewrite Hu in IH. exact IH.
Qed.

#[using="Type"] Theorem den_conv_rt : forall E S M ms model (f : region -> bool) (R0 : region) (fs : list fact) (pv sz : lin) (bs : list Z),
  DEN segs LIMIT model0 mem0 E S M ms model -> sm_own M = [] ->
  In R0 (s_rgs S) -> f R0 = true ->
  (forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> in_shadow w = false) ->
  Forall (fun g => fwf (s_next S) g = true /\ fact_ok E g) fs ->
  lwf (s_next S) pv = true -> lwf (s_next S) sz = true -> 0 < uE E sz -> Z.of_nat (length bs) <= uE E sz ->
  Forall (fun b => 0 <= b < 256) bs ->
  uE E (sm_sp M) <= uE E pv ->
  (forall w, uE E pv <= w < uE E pv + uE E sz ->
     (exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p) /\ mem0 (Z_to_bv 64 w) <> None) \/
     uE E (rg_base R0) <= w < uE E (rg_base R0) + rsz E R0) ->
  (forall k, (k < length bs)%nat ->
     (exists p, In p (sm_frz M) /\ uE E (fst p) <= uE E pv + Z.of_nat k < uE E (fst p) + uE E (snd p)) /\
     mem0 (Z_to_bv 64 (uE E pv + Z.of_nat k)) = Some (Z_to_bv 8 (nth k bs 0))) ->
  DEN segs LIMIT model0 mem0 E (conv_post S f fs pv sz bs) (frz_clear M) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f R0 fs pv sz bs Hd Hon Hin Hf0 Hsh Hfs Hwv Hws Hsz Hlen Hbs Hsp Hpts Hby.
  assert (Hd1 : DEN segs LIMIT model0 mem0 E (drop_post S f) M ms model).
  { apply (den_drop segs LIMIT model0 mem0 E S M ms model f Hd Hon).
    intros R HR HfR w Hw Hz. exfalso. pose proof (dn_zrsh _ _ _ _ _ _ _ _ _ Hd w Hz) as Hs.
    rewrite (Hsh R HR HfR w Hw) in Hs. discriminate. }
  assert (Hd2 : DEN segs LIMIT model0 mem0 E (add_facts (drop_post S f) fs) M ms model) by exact (den_add_facts fs E _ M ms model Hd1 Hfs).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG0 & HD0 & _ & _).
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as HspE.
  pose proof (dn_rl _ _ _ _ _ _ _ _ _ Hd) as Hrl.
  unfold conv_post.
  apply (den_mat_rt segs LIMIT model0 mem0 E _ M ms model pv sz bs Hd2); rewrite ?add_facts_next; cbn [drop_post s_next]; try assumption.
  - intros w Hw. rewrite add_facts_rgs. cbn [drop_post s_rgs].
    destruct (Hpts w Hw) as [(p & Hp & Hwp & Hm0)|HwR].
    + destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp w Hwp) as (Htop & Hout & _).
      split; [exact Htop|]. split.
      * unfold outside in *. rewrite Forall_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hout R HR).
      * unfold rd1. rewrite (frz_restrict segs LIMIT model0 mem0 E S M ms model w Hd (ex_intro _ p (conj Hp Hwp))).
        destruct (mem0 (Z_to_bv 64 w)) as [b|]; [discriminate | exact (fun _ => Hm0 eq_refl)].
    + rewrite Forall_forall in Hrl. destruct (Hrl R0 Hin) as [Hpos [Happ|(_ & _ & Hshw)]].
      2: { destruct (Hshw w HwR) as [Hs _]. rewrite (Hsh R0 Hin Hf0 w HwR) in Hs. discriminate. }
      destruct (Happ w HwR) as (_ & _ & Hw47).
      split; [|split].
      * split; [|lia]. unfold alloc_top, stack_max_size. rewrite HspE. fold (uE E (sm_sp M)). lia.
      * apply (outside_filter_R0 E f (s_rgs S) R0 w HD0 Hin Hf0 HwR). unfold two64. lia.
      * rewrite Forall_forall in HG0.
        pose proof (rg_ok_rd1 E _ R0 (w - uE E (rg_base R0)) (HG0 R0 Hin) ltac:(lia)) as Hr.
        replace (uE E (rg_base R0) + (w - uE E (rg_base R0))) with w in Hr by lia. exact Hr.
  - intros k Hk. destruct (Hby k Hk) as [Hcov Hm].
    unfold rd1. rewrite (frz_restrict segs LIMIT model0 mem0 E S M ms model _ Hd Hcov). rewrite Hm. reflexivity.
Qed.
End Conv.
