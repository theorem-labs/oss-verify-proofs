(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import AgentLib RelSpec MmapSim BWorld ShapeAlg AllocSim RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
From Stdlib Require Classical_Prop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_216 : forall i m o,
  bv_unsigned (in_sysno i) = 216%Z ->
  syscall_spec i m o <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Definition mremap_src_ok (m : Model) (old : word) (old_nZ : Z) : bool :=
  mremap_source_b (m_vmmaps m) old (Z_to_bv 64 old_nZ) old_nZ
  && mremap_backing_uniform_b m old (Z_to_bv 64 old_nZ).

Lemma mremap_outcome : forall old old_size new_size flags i m o,
  bv_unsigned flags = MREMAP_MAYMOVE ->
  (bv_unsigned old mod page_size = 0)%Z ->
  page_align_is0_b new_size = false ->
  page_align_is0_b old_size = false ->
  let old_nZ := page_round_up_Z (bv_unsigned old_size) in
  let new_nZ := page_round_up_Z (bv_unsigned new_size) in
  let old_n := Z_to_bv 64 old_nZ in
  let new_n := Z_to_bv 64 new_nZ in
  mremap_src_ok m old old_nZ = true ->
  mremap_spec old old_size new_size flags i m o <->
  (old_nZ = new_nZ /\ o = Ok (mkEffect old [] []) m [])
  \/ (old_nZ <> new_nZ /\
      ((exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
       \/ (new_nZ < old_nZ /\
           o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
       \/ (old_nZ < new_nZ /\ mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true /\
           o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
       \/ (old_nZ < new_nZ /\ exists dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true /\
           o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []))).
Proof.
  intros old old_size new_size flags i m o Hfl Hal Hnew Hold. cbv zeta. intros Hsrc.
  unfold mremap_spec. rewrite Hfl. change (negb (MREMAP_MAYMOVE =? MREMAP_MAYMOVE)) with false. cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. rewrite Hnew, Hold.
  unfold mremap_src_ok in Hsrc. sys_unfold.
  set (oZ := page_round_up_Z (bv_unsigned old_size)) in *.
  set (nZ := page_round_up_Z (bv_unsigned new_size)) in *.
  destruct (Z.eqb_spec oZ nZ) as [Heq|Hne].
  { (* [comment removed for export] *)
    split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc in *; cbn [negb] in *; inv_sys.
      left. split; [exact Heq| reflexivity].
    - intros [[_ ->]|[Hc _]]; [|exfalso; exact (Hc Heq)].
      eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; reflexivity. }
  destruct (Z.ltb_spec nZ oZ) as [Hlt|Hge].
  { (* [comment removed for export] *)
    split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc in *; cbn [negb] in *; inv_sys.
      + right. split; [exact Hne|]. left. eexists; split; [eassumption|reflexivity].
      + right. split; [exact Hne|]. right. left. split; [exact Hlt|reflexivity].
    - intros [[Hc _]|[_ [(e & He & ->)|[[_ ->]|[[Hc _]|[Hc _]]]]]]; try (exfalso; lia).
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        right. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity. }
  assert (Hgt : oZ < nZ) by lia.
  destruct (mremap_inplace_grow_b m old (Z_to_bv 64 oZ) (Z_to_bv 64 nZ) oZ nZ) eqn:Hig.
  { (* [comment removed for export] *)
    split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc in *; cbn [negb] in *; inv_sys; rewrite ?Hig in *; inv_sys.
      + right. split; [exact Hne|]. left. eexists; split; [eassumption|reflexivity].
      + right. split; [exact Hne|]. right. right. left. split; [exact Hgt|]. split; [reflexivity|reflexivity].
      + right. split; [exact Hne|]. right. right. right. split; [exact Hgt|]. eexists; split; [eassumption|reflexivity].
    - intros [[Hc _]|[_ [(e & He & ->)|[[Hc _]|[(_ & _ & ->)|(_ & dst & Hd & ->)]]]]]; try (exfalso; lia).
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        right. rewrite Hig. left. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        right. rewrite Hig. right. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|]. split; [|reflexivity].
        eexists _, _, _, _. split; [reflexivity|]. split; reflexivity. }
  { (* [comment removed for export] *)
    split.
    - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc in *; cbn [negb] in *; inv_sys; rewrite ?Hig in *; inv_sys.
      + right. split; [exact Hne|]. left. eexists; split; [eassumption|reflexivity].
      + right. split; [exact Hne|]. right. right. right. split; [exact Hgt|]. eexists; split; [eassumption|reflexivity].
    - intros [[Hc _]|[_ [(e & He & ->)|[[Hc _]|[(_ & Hc & ->)|(_ & dst & Hd & ->)]]]]]; try (exfalso; lia); try congruence.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
      + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc. cbn [negb]. split; [|reflexivity].
        right. rewrite Hig. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|]. split; [|reflexivity].
        eexists _, _, _, _. split; [reflexivity|]. split; reflexivity. }
Qed.

Definition brk_r_acfg (md : Model) (req r : word) : Prop :=
  brk_resolution_ok md req r /\ (brk_refusal_b md req r = true -> brk_refusable md req = true).
Arguments brk_r_acfg : simpl never.

Lemma brk_r_acfg_ok : forall md req r, brk_r_acfg md req r -> brk_resolution_ok md req r.
Proof. intros md req r [H _]. exact H. Qed.
#[export] Hint Resolve brk_r_acfg_ok : core.

Lemma brk_r_acfg_inhabited : forall md req, exists r, brk_r_acfg md req r.
Proof.
  intros md req. destruct (brk_refusable md req) eqn:EF.
  - exists (vm_brk (m_vmmaps md)). split; [exact (brk_r_ok_keep md req) | intros _; exact EF].
  - destruct (brk_grant_of_refusable_false md req EF) as (r & Hr & Hnr).
    exists r. split; [exact Hr|]. intros H. rewrite Hnr in H. discriminate H.
Qed.

Definition mremap_can (md : Model) (old on nn : word) (oZ nZ : Z) : Prop :=
  (nZ < oZ)%Z
  \/ ((oZ < nZ)%Z /\ mremap_inplace_grow_b md old on nn oZ nZ = true)
  \/ ((oZ < nZ)%Z /\ exists dst, mremap_fresh_b md oZ nZ old on dst nn = true).

Definition mremap_errno_acfg (md : Model) (old on nn : word) (oZ nZ e : Z) : Prop :=
  In e mremap_errnos /\ ~ mremap_can md old on nn oZ nZ.
Arguments mremap_errno_acfg : simpl never.

Lemma mremap_errno_acfg_In : forall md old on nn oZ nZ e,
  mremap_errno_acfg md old on nn oZ nZ e -> In e mremap_errnos.
Proof. intros md old on nn oZ nZ e [H _]. exact H. Qed.
#[export] Hint Extern 1 (In _ mremap_errnos) =>
  (match goal with H : mremap_errno_acfg _ _ _ _ _ _ _ |- _ => exact (mremap_errno_acfg_In _ _ _ _ _ _ _ H) end) : core.

Lemma mremap_fresh_aligned : forall m oZ nZ old on dst nn,
  mremap_fresh_b m oZ nZ old on dst nn = true -> (bv_unsigned dst mod page_size = 0)%Z.
Proof.
  intros m oZ nZ old on dst nn H. unfold mremap_fresh_b in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. exact H.
Qed.

Lemma mremap_outcome_acfg : forall old old_size new_size flags i m o,
  bv_unsigned (in_sysno i) = 216%Z ->
  in_arg i 0 = old -> in_arg i 1 = old_size -> in_arg i 2 = new_size -> in_arg i 3 = flags ->
  m_halted m = None ->
  bv_unsigned flags = MREMAP_MAYMOVE ->
  (bv_unsigned old mod page_size = 0)%Z ->
  page_align_is0_b new_size = false ->
  page_align_is0_b old_size = false ->
  let old_nZ := page_round_up_Z (bv_unsigned old_size) in
  let new_nZ := page_round_up_Z (bv_unsigned new_size) in
  let old_n := Z_to_bv 64 old_nZ in
  let new_n := Z_to_bv 64 new_nZ in
  mremap_src_ok m old old_nZ = true ->
  syscall_spec_acfg i m o <->
  (old_nZ = new_nZ /\ o = Ok (mkEffect old [] []) m [])
  \/ (old_nZ <> new_nZ /\
      ((exists e, mremap_errno_acfg m old old_n new_n old_nZ new_nZ e /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
       \/ (new_nZ < old_nZ /\
           o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
       \/ (old_nZ < new_nZ /\ mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true /\
           o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
       \/ (old_nZ < new_nZ /\ exists dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true /\
           o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []))).
Proof.
  intros old old_size new_size flags i m o Hno H0 H1 H2 H3 Hh Hfl Hal Hnew Hold. cbv zeta. intros Hsrc.
  assert (Hspec : forall o', syscall_spec i m o' <-> mremap_spec old old_size new_size flags i m o').
  { intros o'. rewrite (syscall_spec_216 i m o' Hno), H0, H1, H2, H3. apply iff_refl. }
  pose proof (fun o' => mremap_outcome old old_size new_size flags i m o' Hfl Hal Hnew Hold Hsrc) as Hout.
  cbv zeta in Hout.
  set (oZ := page_round_up_Z (bv_unsigned old_size)) in *.
  set (nZ := page_round_up_Z (bv_unsigned new_size)) in *.
  assert (Hoff : injected_family_off ACFG i = true).
  { apply (acfg_family_off_no i 216 Hno). apply (proj1 (alloc_no_b_In 216)). reflexivity. }
  assert (Hrold : refusal_b i m old = false).
  { rewrite (refusal_b_216 i m old Hno). exact (ret_in_errnos_ENOMEM_aligned old Hal). }
  assert (Hrip : forall on nn, refusal_b i m (eff_ret (mremap_inplace_effect old on nn oZ nZ)) = false).
  { intros on nn. unfold mremap_inplace_effect. destruct (nZ <? oZ)%Z; exact Hrold. }
  assert (Hrmv : forall on dst, mremap_fresh_b m oZ nZ old on dst (Z_to_bv 64 nZ) = true ->
                   refusal_b i m (eff_ret (mremap_move_effect old on dst oZ nZ)) = false).
  { intros on dst Hd. rewrite (refusal_b_216 i m _ Hno).
    exact (ret_in_errnos_ENOMEM_aligned dst (mremap_fresh_aligned _ _ _ _ _ _ _ Hd)). }
  assert (Hcan : oZ <> nZ -> mremap_can m old (Z_to_bv 64 oZ) (Z_to_bv 64 nZ) oZ nZ ->
            exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false).
  { intros Hne [Hlt | [(Hlt & Hg) | (Hlt & dst & Hd)]].
    - eexists _, _, _. split.
      + apply (proj2 (Hspec _)), (proj2 (Hout _)). right. split; [exact Hne|]. right. left.
        split; [exact Hlt | reflexivity].
      + apply Hrip.
    - eexists _, _, _. split.
      + apply (proj2 (Hspec _)), (proj2 (Hout _)). right. split; [exact Hne|]. right. right. left.
        split; [exact Hlt|]. split; [exact Hg | reflexivity].
      + apply Hrip.
    - eexists _, _, _. split.
      + apply (proj2 (Hspec _)), (proj2 (Hout _)). right. split; [exact Hne|]. right. right. right.
        split; [exact Hlt|]. exists dst. split; [exact Hd | reflexivity].
      + exact (Hrmv _ dst Hd). }
  split.
  - intros [Hs Hok].
    destruct (proj1 (Hout o) (proj1 (Hspec o) Hs)) as [Heq | [Hne [(e & He & ->) | Hrest]]].
    + left. exact Heq.
    + right. split; [exact Hne|]. left. exists e. split; [|reflexivity]. split; [exact He|].
      intros HC. destruct (Hcan Hne HC) as (eff' & m'' & evs' & Hs' & Hnr).
      apply (Hok Hh). split; [exact Hoff|]. split.
      * rewrite (refusal_b_216 i m _ Hno). exact (ret_in_errnos_errno _ _ He).
      * exists eff', m'', evs'. split; [exact Hs' | exact Hnr].
    + right. split; [exact Hne|]. right. exact Hrest.
  - intros Hc. split.
    + apply (proj2 (Hspec o)), (proj2 (Hout o)).
      destruct Hc as [Heq | [Hne [(e & [He _] & ->) | Hrest]]].
      * left. exact Heq.
      * right. split; [exact Hne|]. left. exists e. split; [exact He | reflexivity].
      * right. split; [exact Hne|]. right. exact Hrest.
    + destruct Hc as [(Heq & ->) | [Hne [(e & [He Hnc] & ->) | Hrest]]].
      * cbn [spec_step_ok]. intros _. apply spurious_refusal_not_refusal. exact Hrold.
      * cbn [spec_step_ok]. intros _ (_ & _ & (eff' & m'' & evs' & Hs' & Hnr)).
        destruct (proj1 (Hout _) (proj1 (Hspec _) Hs')) as [(Heq' & _) | [_ [(e' & He' & Heq') | Hrest']]].
        -- exact (Hne Heq').
        -- injection Heq' as Heff _ _. subst eff'.
           rewrite (refusal_b_216 i m _ Hno) in Hnr.
           change (eff_ret (mkEffect (errno_ret e') [] [])) with (errno_ret e') in Hnr.
           rewrite (ret_in_errnos_errno _ _ He') in Hnr. discriminate Hnr.
        -- apply Hnc. destruct Hrest' as [(Hlt & _) | [(Hlt & Hg & _) | (Hlt & dst & Hd & _)]].
           ++ left. exact Hlt.
           ++ right. left. split; [exact Hlt | exact Hg].
           ++ right. right. split; [exact Hlt|]. exists dst. exact Hd.
      * destruct Hrest as [(Hlt & ->) | [(Hlt & Hg & ->) | (Hlt & dst & Hd & ->)]];
          cbn [spec_step_ok]; intros _; apply spurious_refusal_not_refusal.
        -- apply Hrip.
        -- apply Hrip.
        -- exact (Hrmv _ dst Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {BW : BWorld}.

Lemma t_alt_const : forall (I : Type) (i0 : I) (T : TSet),
  T [] -> t_eq (t_alt (fun _ : I => t_emit [] T)) T.
Proof.
  intros I i0 T HT tr. split.
  - intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
  - intros H. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) H).
Qed.

(* [comment removed for export] *)
Lemma sysnode_sstep : forall ms md x8 (R : SyscallEffect -> Model -> Prop),
  m_halted md = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) md o <-> exists eff md', R eff md' /\ o = Ok eff md' []) ->
  (forall eff md', R eff md' -> m_halted md' = None /\ m_vm_lazy md' = []) ->
  forall eff md', R eff md' ->
  sstep_cfg segs ACFG (mkCfg ms md) [] (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) md')).
Proof.
  intros ms md x8 R Hh Hsvc Hchar Hinv eff md' HR.
  destruct (Hinv eff md' HR) as [Hh' Hl'].
  eapply (sstep_cfg_syscall_acfg segs ms md x8 eff md' md' []); [exact Hh | exact Hsvc | | exact Hh' |].
  - apply (proj2 (Hchar _)). exists eff, md'. split; [exact HR | reflexivity].
  - apply materialize_model_accesses_no_lazy. exact Hl'.
Qed.

(* [comment removed for export] *)
Lemma rz_sysnode0 : forall ms md x8 (R : SyscallEffect -> Model -> Prop) T,
  m_halted md = None -> m_vm_lazy md = [] ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) md o <-> exists eff md', R eff md' /\ o = Ok eff md' []) ->
  (forall eff md', R eff md' -> m_halted md' = None /\ m_vm_lazy md' = []) ->
  (exists eff md', R eff md') ->
  (forall eff md', R eff md' -> realizes0 segs (mkCfg (advance_past_svc (apply_effect ms eff)) md') T) ->
  realizes0 segs (mkCfg ms md) T.
Proof.
  (intros ms md x8 R T Hh Hl Hsvc Hchar Hinv; (first [ intro dR_15; dex2 dR_15 as eff0 md0; rename dR_15 into HR0 | intro dR_15; dand3 dR_15 as eff0 md0 HR0 | intros (eff0 & md0 & HR0) ]); intros HK).
  set (I := {p : SyscallEffect * Model | R (fst p) (snd p)}).
  set (nx := fun i : I => mkCfg (advance_past_svc (apply_effect ms (fst (proj1_sig i)))) (snd (proj1_sig i))).
  assert (HT : T []).
  { eapply realizes0_nonempty. apply (HK eff0 md0 HR0). }
  apply (rz_conseq0 segs (mkCfg ms md) (t_alt (fun i : I => t_emit [] T))).
  - apply (rz_node0 segs (mkCfg ms md) I (fun _ => []) nx (fun _ => T) (exist _ (eff0, md0) HR0)).
    + split.
      * intros [[eff md'] HR]. unfold nx. cbn [proj1_sig fst snd].
        exact (sysnode_sstep ms md x8 R Hh Hsvc Hchar Hinv eff md' HR).
      * intros e st Hss.
        pose proof (sstep_cfg_sys_inv_acfg segs ms md x8 e st Hsvc Hss) as Hinv'. cbv zeta in Hinv'.
        destruct Hinv' as [(eff & m' & evs0 & Hs & Hh' & Hm)
                          | [(eff & m' & evs0 & code & Hs & Hh' & Hk & -> & ->)
                          | [(eff & m' & evs0 & sig & Hs & Hk & -> & ->) | (Hs & -> & ->)]]].
        -- (* [comment removed for export] *)
           (* [comment removed for export] *)
           destruct (proj1 (Hchar _) Hs) as (eff' & md' & HR & Heq).
           apply Ok_inj in Heq as (-> & -> & ->).
           rewrite (materialize_model_accesses_no_lazy _ _ (proj2 (Hinv _ _ HR))) in Hm.
           destruct Hm as [-> ->].
           exists (exist _ (eff', md') HR). split; reflexivity.
        -- (* [comment removed for export] *)
           exfalso. destruct (proj1 (Hchar _) Hs) as (eff' & md' & HR & Heq).
           apply Ok_inj in Heq as (-> & -> & ->).
           rewrite (proj1 (Hinv _ _ HR)) in Hh'. discriminate Hh'.
        -- (* [comment removed for export] *)
           exfalso. destruct (proj1 (Hchar _) Hs) as (eff' & md' & HR & Heq).
           apply Ok_inj in Heq as (-> & -> & ->).
           rewrite (m_killed_of_m_halted_none _ (proj1 (Hinv _ _ HR))) in Hk. discriminate Hk.
        -- (* [comment removed for export] *)
           exfalso. destruct (proj1 (Hchar _) Hs) as (eff' & md' & HR & Heq).
           exact (Unmodeled_Ok _ _ _ Heq).
    + intros [[eff md'] HR]. unfold nx. cbn [proj1_sig fst snd]. apply HK. exact HR.
  - apply (t_alt_const I (exist _ (eff0, md0) HR0) T HT).
Qed.

(* [comment removed for export] *)
Lemma rz_sysnode : forall ms md x8 (R : SyscallEffect -> Model -> Prop) T,
  m_halted md = None -> m_vm_lazy md = [] ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) md o <-> exists eff md', R eff md' /\ o = Ok eff md' []) ->
  (forall eff md', R eff md' -> m_halted md' = None /\ m_vm_lazy md' = []) ->
  (exists eff md', R eff md') ->
  (forall eff md', R eff md' -> bw_gate (sys_input segs ms x8) md ->
     realizes segs (mkCfg (advance_past_svc (apply_effect ms eff)) md') T) ->
  realizes segs (mkCfg ms md) T.
Proof.
  intros ms md x8 R T Hh Hl Hsvc Hchar Hinv Hex HK. constructor. intros Hne.
  assert (Hgate : bw_gate (sys_input segs ms x8) md).
  { unfold bw_gate. destruct bw_on eqn:EW; [|exact I].
    destruct (alloc_budget_refused_b (sys_input segs ms x8) md) eqn:E; [|reflexivity].
    exfalso. apply (never_excused_here segs (mkCfg ms md) Hne). unfold bw_excuse. rewrite EW.
    split; [exact Hh|]. right. exists x8. split; [exact Hsvc | left; exact E]. }
  apply (rz_sysnode0 ms md x8 R T Hh Hl Hsvc Hchar Hinv Hex).
  intros eff md' HR. apply (rz_unwrap segs _ T (HK eff md' HR Hgate)).
  exact (never_excused_step segs _ [] _ Hne (sysnode_sstep ms md x8 R Hh Hsvc Hchar Hinv eff md' HR)).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w (z : Z) : word := Z_to_bv 64 z.
Definition rlen (len : Z) : Z := page_round_up_Z (bv_unsigned (w len)).
Definition wlen (len : Z) : word := Z_to_bv 64 (rlen len).

Definition NMAP_ANON : Z := 34.          (* [comment removed for export] *)
Definition NMAP_ANON_FIXED : Z := 50.    (* [comment removed for export] *)
Definition NPROT_RW : Z := 3.

Definition nsafe (n : node) (md : Model) : Prop :=
  let h := m_vmmaps md in
  match n with
  | NBrk req => True
  | NMmap addr len prot flags =>
      (flags = NMAP_ANON /\ (prot = NPROT_RW \/ prot = 0) /\ w len <> w 0)
      \/ (flags = NMAP_ANON_FIXED /\ prot = 0 /\ w len <> w 0 /\
          (bv_unsigned (w addr) mod page_size = 0)%Z /\ (0 < bv_unsigned (w addr))%Z /\
          (0 < bv_unsigned (w len))%Z /\ (bv_unsigned (w addr) + rlen len <= alloc_top h)%Z /\   (* [comment removed for export] *)
          region_free (vm_reserved h) (w addr) (wlen len) = true /\
          map_contains (vm_maps h) (w addr) (wlen len) = true)
  | NMunmap addr len =>
      (bv_unsigned (w addr) mod page_size = 0)%Z /\ w len <> w 0 /\
      (bv_unsigned (w addr) + rlen len <= TASK_SIZE)%Z /\   (* [comment removed for export] *)
      map_has (vm_maps h) (w addr) (wlen len) = true
  | NMprotect addr len prot =>
      prot = NPROT_RW /\ (bv_unsigned (w addr) mod page_size = 0)%Z /\ (0 < bv_unsigned (w len))%Z /\
      (bv_unsigned (w addr) + rlen len < two_pow_64)%Z /\
      map_contains (vm_noaccess h) (w addr) (wlen len) = true /\
      map_contains (vm_maps h) (w addr) (wlen len) = true
  | NMremap old oldlen newlen flags =>
      flags = MREMAP_MAYMOVE /\ (bv_unsigned (w old) mod page_size = 0)%Z /\
      page_align_is0_b (w newlen) = false /\ page_align_is0_b (w oldlen) = false /\
      mremap_src_ok md (w old) (rlen oldlen) = true
  | _ => False
  end.

Definition nstep (n : node) (md : Model) (eff : resp) (md' : Model) : Prop :=
  let h := m_vmmaps md in
  match n with
  | NBrk req =>
      exists r, brk_r_acfg md (w req) r /\
        eff = mkEffectU r [] (brk_zeros (w req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] [] /\
        md' = brk_model (w req) r md
  | NMmap addr len prot flags =>
      (* [comment removed for export] *)
      if (flags =? NMAP_ANON)%Z then
        if (prot =? NPROT_RW)%Z then
             (exists e, In e (mmap_errnos_when (grant_refusable md (rlen len))) /\ eff = mkEffect (errno_ret e) [] [] /\ md' = md)
          \/ (exists a, grant_ok (w addr) md a (rlen len) = true /\
                eff = mkEffect a [] [(a, wlen len)] /\ md' = mmap_model a (wlen len) md)
        else (exists e, In e (mmap_errnos_when (mmap_reserve_refusable md (rlen len))) /\ eff = mkEffect (errno_ret e) [] [] /\ md' = md)
          \/ (exists a, grant_ok_na (w addr) md a (rlen len) = true /\
                eff = mkEffectU a [] [] [(a, wlen len)] [] [] /\ md' = noaccess_model a (wlen len) md)
      else   (exists e, In e (mmap_errnos_when false) /\ eff = mkEffect (errno_ret e) [] [] /\ md' = md)
          \/ (eff = mkEffectU (w addr) [] [] [(w addr, wlen len)] [] [] /\ md' = fixed_noaccess_model (w addr) (wlen len) md)
          (* [comment removed for export] *)
          \/ (spec_destructive_fixed /\
              exists e, In e mmap_errnos /\ eff = mkEffectU (errno_ret e) [] [] [(w addr, wlen len)] [] [] /\
                md' = fixed_destroyed_model (w addr) (wlen len) md)
  | NMunmap addr len =>
      eff = mkEffectU (w 0) [] [] [(w addr, wlen len)] [] [] /\ md' = munmap_model (w addr) (wlen len) md
  | NMprotect addr len prot =>
         (exists e, In e (mprotect_errnos_when (mprotect_refusable md (w addr) (wlen len))) /\
                    eff = mkEffect (errno_ret e) [] [] /\ md' = md)   (* [comment removed for export] *)
      \/ (mprotect_budget_ok md (w addr) (wlen len) = true /\
          eff = mkEffect (w 0) [] [(w addr, wlen len)] /\ md' = mprotect_model (w addr) (wlen len) md)
  | NMremap old oldlen newlen flags =>
      let oZ := rlen oldlen in let nZ := rlen newlen in
      let on := wlen oldlen in let nn := wlen newlen in
         (oZ = nZ /\ eff = mkEffect (w old) [] [] /\ md' = md)
      \/ (oZ <> nZ /\
          ((exists e, mremap_errno_acfg md (w old) on nn oZ nZ e /\ eff = mkEffect (errno_ret e) [] [] /\ md' = md)
           \/ (nZ < oZ /\ eff = mremap_inplace_effect (w old) on nn oZ nZ /\ md' = mremap_model_next md (w old) on (w old) nn)
           \/ (oZ < nZ /\ mremap_inplace_grow_b md (w old) on nn oZ nZ = true /\
               eff = mremap_inplace_effect (w old) on nn oZ nZ /\ md' = mremap_model_next md (w old) on (w old) nn)
           \/ (oZ < nZ /\ exists dst, mremap_fresh_b md oZ nZ (w old) on dst nn = true /\
               eff = mremap_move_effect (w old) on dst oZ nZ /\ md' = mremap_model_next md (w old) on dst nn)))
  | _ => False
  end.

(* [comment removed for export] *)
Definition KI (md : Model) : Prop := m_halted md = None /\ m_vm_lazy md = [].

(* [comment removed for export] *)
Definition nbudget_refused (n : node) (md : Model) : bool :=
  match node_input n with Some i => alloc_budget_refused_b i md | None => false end.

Definition bw_gate_n (n : node) (md : Model) : Prop :=
  if bw_on then nbudget_refused n md = false else True.

Lemma bw_gate_n_off : forall n md, bw_on = false -> bw_gate_n n md.
Proof. intros n md E. unfold bw_gate_n. rewrite E. exact I. Qed.

(* [comment removed for export] *)
Lemma bw_gate_n_mmap_rw : forall addr len md,
  bw_on = true -> w len <> w 0 ->
  bw_gate_n (NMmap addr len NPROT_RW NMAP_ANON) md ->
  (vm_backing_used md + rlen len <=? vm_limit (m_vmmaps md))%Z = true.
Proof.
  intros addr len md E Hlen H. unfold bw_gate_n in H. rewrite E in H.
  unfold nbudget_refused in H. cbn [node_input] in H.
  rewrite abr_mmap in H by reflexivity. cbn [in_arg pure_input in_args nth] in H.
  unfold mmap_budget_refused_b in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 NMAP_ANON)) with true in H. cbn [negb] in H.
  assert (Hz : w_is0 (Z_to_bv 64 len) = false).
  { destruct (w_is0 (Z_to_bv 64 len)) eqn:E0; [| reflexivity]. exfalso. apply Hlen.
    unfold w_is0, bv_eqb in E0. apply Z.eqb_eq in E0. unfold w. apply bv_eq. exact E0. }
  rewrite Hz in H.
  change (mmap_modeled_b (Z_to_bv 64 NPROT_RW) (Z_to_bv 64 NMAP_ANON) (Z_to_bv 64 0)) with true in H.
  cbv zeta in H. unfold mmap_noreserve_backed_ok in H.
  change (mmap_noreserve_b (Z_to_bv 64 NMAP_ANON)) with false in H.
  apply negb_false_iff in H. exact H.
Qed.

Lemma bw_gate_n_mprotect : forall addr len md,
  bw_on = true -> nsafe (NMprotect addr len NPROT_RW) md ->
  bw_gate_n (NMprotect addr len NPROT_RW) md ->
  mprotect_budget_ok md (w addr) (wlen len) = true.
Proof.
  intros addr len md E HS H. unfold bw_gate_n in H. rewrite E in H.
  unfold nbudget_refused in H. cbn [node_input] in H.
  rewrite abr_mprotect in H by reflexivity. cbn [in_arg pure_input in_args nth] in H.
  cbn [nsafe] in HS. destruct HS as (_ & Hal & Hlpos & Hnw & Hna & Hma).
  unfold mprotect_budget_refused_b in H.
  change (mprotect_grows_conflict_b (Z_to_bv 64 NPROT_RW)) with false in H.
  fold (w addr) in H. fold (w len) in H.
  rewrite (proj2 (Z.eqb_eq _ _) Hal) in H. cbn [negb] in H.
  assert (Hz : w_is0 (w len) = false) by (apply Syscall.w_is0_pos; exact Hlpos).
  rewrite Hz in H.
  fold (rlen len) in H.
  rewrite (proj2 (Z.leb_gt _ _) Hnw) in H.
  change (mprotect_modeled_b (Z_to_bv 64 NPROT_RW)) with true in H.
  cbv zeta in H. fold (wlen len) in H. rewrite Hna, Hma in H. cbn [andb] in H.
  apply negb_false_iff in H. exact H.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vmmaps_KI : forall h md, KI md -> KI (with_vmmaps h md).
Proof. intros h md [H1 H2]. split; [rewrite with_vmmaps_halted; exact H1 | rewrite with_vmmaps_lazy'; exact H2]. Qed.

Lemma vm_forget_range_KI : forall lo hi md, KI md -> KI (vm_forget_range lo hi md).
Proof.
  intros lo hi md [H1 H2]. split; [rewrite vm_forget_range_halted; exact H1 | apply vm_forget_range_lazy_nil; exact H2].
Qed.

Lemma forget_vm_ranges_KI : forall l md, KI md -> KI (forget_vm_ranges l md).
Proof.
  induction l as [|[a n] l IH]; intros md HK; cbn; [exact HK|]. apply IH. apply vm_forget_range_KI. exact HK.
Qed.

Lemma mremap_model_next_KI : forall md old on dst nn, KI md -> KI (mremap_model_next md old on dst nn).
Proof.
  intros md old on dst nn [H1 H2]. unfold mremap_model_next, vm_resize_backing, mremap_source_lazy_b.
  rewrite with_vmmaps_lazy', H2. cbn [map_contains maps_subtract]. unfold with_vm_backing, KI. cbn.
  split; [| reflexivity]. unfold m_halted in *. cbn. exact H1.
Qed.

Lemma nstep_KI : forall n md eff md', KI md -> nstep n md eff md' -> KI md'.
Proof.
  intros n md eff md' HK HS. destruct n; cbn -[brk_model mmap_model noaccess_model fixed_noaccess_model
    fixed_destroyed_model munmap_model mprotect_model mremap_model_next Z.eqb] in HS; try contradiction.
  - (first [ dex1 HS as r; dand3 HS as Hr -> -> | dand4 HS as r Hr -> -> | destruct HS as (r & Hr & -> & ->) ]). unfold brk_model, with_brk_next. apply forget_vm_ranges_KI, with_vmmaps_KI, HK.
  - destruct (flags =? NMAP_ANON)%Z; [destruct (prot =? NPROT_RW)%Z|].
    + destruct HS as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [exact HK|]. unfold mmap_model. apply with_vmmaps_KI, HK.
    + destruct HS as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [exact HK|]. unfold noaccess_model. apply with_vmmaps_KI, HK.
    + destruct HS as [(e & _ & _ & ->)|[(_ & ->)|(_ & e & _ & _ & ->)]]; [exact HK| |].
      * unfold fixed_noaccess_model. apply vm_forget_range_KI, with_vmmaps_KI, HK.
      * unfold fixed_destroyed_model. apply vm_forget_range_KI, with_vmmaps_KI, HK.
  - destruct HS as [-> ->]. destruct HK as [H1 H2].
    split; [rewrite munmap_model_halted; exact H1 | apply munmap_model_no_lazy; exact H2].
  - destruct HS as [(e & _ & _ & ->)|(_ & _ & ->)]; [exact HK|]. unfold mprotect_model. apply with_vmmaps_KI, HK.
  - destruct HS as [(_ & _ & ->)|[_ [(e & _ & _ & ->)|[(_ & _ & ->)|[(_ & _ & _ & ->)|(_ & dst & _ & _ & ->)]]]]];
      try exact HK; apply mremap_model_next_KI; exact HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_inhabited : forall n md, nsafe n md -> exists eff md', nstep n md eff md'.
Proof.
  intros n md HS. destruct n; cbn in HS; try contradiction;
    cbn -[brk_model mmap_model noaccess_model fixed_noaccess_model fixed_destroyed_model munmap_model
          mprotect_model mremap_model_next Z.eqb grant_ok grant_ok_na brk_resolution_ok].
  - (* [comment removed for export] *)
    destruct (brk_r_acfg_inhabited md (w req)) as [r Hr].
    eexists _, _. exists r. split; [exact Hr | split; reflexivity].
  - (* [comment removed for export] *)
    destruct (flags =? NMAP_ANON)%Z; [destruct (prot =? NPROT_RW)%Z|].
    + destruct (grant_refusable md (rlen len)) eqn:ER.
      * exists (mkEffect (errno_ret ENOMEM) [] []), md. left. exists ENOMEM. auto using ENOMEM_in_mmap_errnos.
      * destruct (proj1 (grant_refusable_false_iff (w addr) md (rlen len)) ER) as [a Ha].
        eexists _, _. right. exists a. split; [exact Ha|]. split; reflexivity.
    + destruct (mmap_reserve_refusable md (rlen len)) eqn:ER.
      * exists (mkEffect (errno_ret ENOMEM) [] []), md. left. exists ENOMEM. auto using ENOMEM_in_mmap_errnos.
      * destruct (proj1 (reserve_refusable_false_iff (w addr) md (rlen len)) ER) as [a Ha].
        eexists _, _. right. exists a. split; [exact Ha|]. split; reflexivity.
    + eexists _, _. right. left. split; reflexivity.
  - eexists _, _. split; reflexivity.
  - destruct (mprotect_budget_ok md (w addr) (wlen len)) eqn:EB.
    + eexists _, _. right. split; [reflexivity|]. split; reflexivity.
    + exists (mkEffect (errno_ret ENOMEM) [] []), md. left. exists ENOMEM.
      unfold mprotect_refusable. rewrite EB. auto using ENOMEM_in_mprotect_errnos.
  - destruct (Z.eq_dec (rlen oldlen) (rlen newlen)).
    + eexists _, _. left. split; [exact e|]. split; reflexivity.
    + destruct (Classical_Prop.classic (mremap_can md (w old) (wlen oldlen) (wlen newlen) (rlen oldlen) (rlen newlen))) as [Hc | Hc].
      * destruct Hc as [Hlt | [(Hlt & Hg) | (Hlt & dst & Hd)]].
        -- eexists _, _. right. split; [exact n|]. right. left. split; [exact Hlt|]. split; reflexivity.
        -- eexists _, _. right. split; [exact n|]. right. right. left. split; [exact Hlt|]. split; [exact Hg|]. split; reflexivity.
        -- eexists _, _. right. split; [exact n|]. right. right. right. split; [exact Hlt|]. exists dst. split; [exact Hd|]. split; reflexivity.
      * exists (mkEffect (errno_ret ENOMEM) [] []), md. right. split; [exact n|]. left. exists ENOMEM.
        split; [split; [left; reflexivity | exact Hc]|]. split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nrefusable (n : node) (md : Model) : bool :=
  match n with
  | NMmap addr len prot flags =>
      if (flags =? NMAP_ANON)%Z then
        if (prot =? NPROT_RW)%Z then grant_refusable md (rlen len)
        else mmap_reserve_refusable md (rlen len)
      else false
  | NMprotect addr len prot => mprotect_refusable md (w addr) (wlen len)
  | _ => false
  end.

Definition nstep_nf (n : node) (md : Model) (eff : resp) (md' : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      if (flags =? NMAP_ANON)%Z then
        if (prot =? NPROT_RW)%Z then
          exists a, grant_ok (w addr) md a (rlen len) = true /\
                eff = mkEffect a [] [(a, wlen len)] /\ md' = mmap_model a (wlen len) md
        else
          exists a, grant_ok_na (w addr) md a (rlen len) = true /\
                eff = mkEffectU a [] [] [(a, wlen len)] [] [] /\ md' = noaccess_model a (wlen len) md
      else eff = mkEffectU (w addr) [] [] [(w addr, wlen len)] [] [] /\ md' = fixed_noaccess_model (w addr) (wlen len) md
  | NMprotect addr len prot =>
      mprotect_budget_ok md (w addr) (wlen len) = true /\
      eff = mkEffect (w 0) [] [(w addr, wlen len)] /\ md' = mprotect_model (w addr) (wlen len) md
  | _ => nstep n md eff md'
  end.

Lemma nstep_nf_nstep : forall n md eff md', nstep_nf n md eff md' -> nstep n md eff md'.
Proof.
  intros n md eff md' H. destruct n; cbn -[Z.eqb] in H |- *; try exact H.
  - destruct (flags =? NMAP_ANON)%Z; [destruct (prot =? NPROT_RW)%Z|].
    + right. exact H.
    + right. exact H.
    + right. left. exact H.
  - right. exact H.
Qed.

Lemma nstep_nf_iff : forall n md eff md',
  nrefusable n md = false -> (nstep n md eff md' <-> nstep_nf n md eff md').
Proof.
  intros n md eff md' NR. split; [|apply nstep_nf_nstep].
  intros H. destruct n; cbn -[Z.eqb] in H, NR |- *; try exact H.
  - destruct (flags =? NMAP_ANON)%Z; [destruct (prot =? NPROT_RW)%Z|].
    + rewrite NR in H. destruct H as [(e & He & _)|H]; [contradiction | exact H].
    + rewrite NR in H. destruct H as [(e & He & _)|H]; [contradiction | exact H].
    + destruct H as [(e & He & _)|[H|(SDF & _)]]; [contradiction | exact H |].
      exfalso. exact (spec_destructive_fixed_false md SDF).
  - rewrite NR in H. destruct H as [(e & He & _)|H]; [contradiction | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gpr0 : forall ms, ms_gpr ms 0 = areg ms 10. Proof. reflexivity. Qed.
Lemma gpr1 : forall ms, ms_gpr ms 1 = areg ms 11. Proof. reflexivity. Qed.
Lemma gpr2 : forall ms, ms_gpr ms 2 = areg ms 12. Proof. reflexivity. Qed.
Lemma gpr3 : forall ms, ms_gpr ms 3 = areg ms 13. Proof. reflexivity. Qed.
Lemma gpr4 : forall ms, ms_gpr ms 4 = areg ms 14. Proof. reflexivity. Qed.
Lemma gpr5 : forall ms, ms_gpr ms 5 = areg ms 15. Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma w_unsigned : forall z, w (bv_unsigned (w z)) = w z.
Proof. intros z. unfold w. apply Z_to_bv_bv_unsigned. Qed.

Lemma at_node_outcome : forall n ms md,
  at_node segs n ms -> m_halted md = None -> nsafe n md ->
  exists x8, ms_svc_pending ms = Some x8 /\
    forall o, syscall_spec_acfg (sys_input segs ms x8) md o <-> exists eff md', nstep n md eff md' /\ o = Ok eff md' [].
Proof.
  intros n ms md HA Hh HS. destruct n; cbn in HA, HS; try contradiction.
  - (* [comment removed for export] *)
    destruct HA as [Hsvc H10]. exists (Z_to_bv 64 214). split; [exact Hsvc|]. intros o.
    rewrite (brk_outcome_si segs ms _ md o) by first [exact Hh | apply u64_lit; lia]. rewrite gpr0, H10. cbn [nstep].
    split.
    + intros (r & Hr & Hf & ->). eexists _, _. split; [exists r; split; [split; [exact Hr | exact Hf] | split; reflexivity] | reflexivity].
    + intros (eff & md' & (r & [Hr Hf] & -> & ->) & ->). exists r. split; [exact Hr|]. split; [exact Hf | reflexivity].
  - (* [comment removed for export] *)
    (first [ dand7 HA as Hsvc H10 H11 H12 H13 H14 H15 | destruct HA as (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) ]). exists (Z_to_bv 64 222). split; [exact Hsvc|].
    destruct HS as [(-> & Hprot & Hlen)|(-> & -> & Hlen & Hal & Hpos & Hlpos & Hce & Hrf & Hmc)].
    + (* [comment removed for export] *)
      cbn [nstep]. change (NMAP_ANON =? NMAP_ANON)%Z with true. cbn match.
      destruct Hprot as [-> | ->].
      * change (NPROT_RW =? NPROT_RW)%Z with true. cbn match. intros o.
        assert (Hargs : mmap_args_ok ms).
        { unfold mmap_args_ok. rewrite gpr1, gpr2, gpr3, gpr4, gpr5, H11, H12, H13, H14, H15. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. exact Hlen. }
        rewrite (mmap_outcome_si segs ms _ md o ltac:(apply u64_lit; lia) Hh Hargs). rewrite gpr0, gpr1, H10, H11.
        unfold page_round_up, rlen, wlen. split.
        -- intros [(e & He & ->)|(a & Ha & ->)]; eexists _, _; (split; [|reflexivity]); [left; exists e| right; exists a]; auto.
        -- ((first [ intro dR_18; dex2 dR_18 as eff md'; destruct dR_18 as [[(e & He & -> & ->)|(a & Ha & -> & ->)] ->] | intro dR_18; dand4 dR_18 as eff md' [(e & He & -> & ->)|(a & Ha & -> & ->)] -> | intros (eff & md' & [(e & He & -> & ->)|(a & Ha & -> & ->)] & ->) ])); [left; exists e| right; exists a]; auto.
      * change (0 =? NPROT_RW)%Z with false. cbn match. intros o.
        assert (Hargs : mmap_noaccess_args_ok ms).
        { unfold mmap_noaccess_args_ok. rewrite gpr1, gpr2, gpr3, gpr4, gpr5, H11, H12, H13, H14, H15. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. exact Hlen. }
        rewrite (mmap_noaccess_outcome_si segs ms _ md ltac:(apply u64_lit; lia) Hh Hargs o). rewrite gpr0, gpr1, H10, H11.
        unfold rlen, wlen. split.
        -- intros [(e & He & ->)|(a & Ha & ->)]; eexists _, _; (split; [|reflexivity]); [left; exists e| right; exists a]; auto.
        -- ((first [ intro dR_19; dex2 dR_19 as eff md'; destruct dR_19 as [[(e & He & -> & ->)|(a & Ha & -> & ->)] ->] | intro dR_19; dand4 dR_19 as eff md' [(e & He & -> & ->)|(a & Ha & -> & ->)] -> | intros (eff & md' & [(e & He & -> & ->)|(a & Ha & -> & ->)] & ->) ])); [left; exists e| right; exists a]; auto.
    + (* [comment removed for export] *)
      cbn [nstep]. change (NMAP_ANON_FIXED =? NMAP_ANON)%Z with false. cbn match. intros o.
      assert (Hargs : mmap_fixed_args_ok ms).
      { unfold mmap_fixed_args_ok. rewrite gpr1, gpr2, gpr3, gpr4, gpr5, H11, H12, H13, H14, H15. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. exact Hlen. }
      pose proof (mmap_fixed_outcome_si segs ms _ md (w addr) (bv_unsigned (w len)) ltac:(apply u64_lit; lia) Hh Hargs
                    ltac:(rewrite gpr0; exact H10) Hal Hpos ltac:(rewrite gpr1, H11; symmetry; apply w_unsigned) Hlpos Hce Hrf Hmc o) as E.
      cbv zeta in E. rewrite E. unfold rlen, wlen. split.
      * intros [(e & He & ->)|[->|(SDF & e & He & ->)]]; eexists _, _; (split; [|reflexivity]);
          [left; exists e; auto| right; left; auto| right; right; split; [exact SDF| exists e; auto]].
      * ((first [ intro dR_20; dex2 dR_20 as eff md'; destruct dR_20 as [[(e & He & -> & ->)|[(-> & ->)|(SDF & e & He & -> & ->)]] ->] | intro dR_20; dand4 dR_20 as eff md' [(e & He & -> & ->)|[(-> & ->)|(SDF & e & He & -> & ->)]] -> | intros (eff & md' & [(e & He & -> & ->)|[(-> & ->)|(SDF & e & He & -> & ->)]] & ->) ]));
          [left; exists e; auto| right; left; reflexivity| right; right; split; [exact SDF| exists e; auto]].
  - (* [comment removed for export] *)
    (first [ dand3 HA as Hsvc H10 H11 | destruct HA as (Hsvc & H10 & H11) ]). exists (Z_to_bv 64 215). split; [exact Hsvc|]. intros o.
    rewrite (acfg_si_nonalloc segs ms (Z_to_bv 64 215) md o) by first [reflexivity | rewrite u64_lit by lia; reflexivity].
    (first [ dand4 HS as Hal Hlen Hnw Hhas | destruct HS as (Hal & Hlen & Hnw & Hhas) ]).
    assert (Hargs : munmap_args_ok ms md).
    { unfold munmap_args_ok. rewrite gpr0, gpr1, H10, H11. unfold page_round_up. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. }
    rewrite (munmap_outcome_si segs ms _ md o ltac:(apply u64_lit; lia) Hargs).
    unfold munmap_eff, page_round_up. rewrite gpr0, gpr1, H10, H11. cbn [nstep]. unfold rlen, wlen. split.
    + intros ->. eexists _, _. split; [split; reflexivity| reflexivity].
    + ((first [ intro dR_21; dex2 dR_21 as eff md'; destruct dR_21 as [[-> ->] ->] | intro dR_21; dand4 dR_21 as eff md' [-> ->] -> | intros (eff & md' & [-> ->] & ->) ])). reflexivity.
  - (* [comment removed for export] *)
    (first [ dand4 HA as Hsvc H10 H11 H12 | destruct HA as (Hsvc & H10 & H11 & H12) ]). exists (Z_to_bv 64 226). split; [exact Hsvc|]. intros o.
    (first [ dand6 HS as -> Hal Hlpos Hnw Hna Hma | destruct HS as (-> & Hal & Hlpos & Hnw & Hna & Hma) ]).
    pose proof (mprotect_outcome_si segs ms _ md (w addr) (bv_unsigned (w len)) ltac:(apply u64_lit; lia) Hh
                  ltac:(rewrite gpr0; exact H10) Hal ltac:(rewrite gpr1, H11; symmetry; apply w_unsigned) Hlpos Hnw
                  ltac:(rewrite gpr2; exact H12) Hna Hma o) as E.
    cbv zeta in E. rewrite E. cbn [nstep]. unfold rlen, wlen. split.
    + intros [(e & He & ->)|(Hb & ->)]; eexists _, _; (split; [|reflexivity]); [left; exists e; auto| right; auto].
    + ((first [ intro dR_22; dex2 dR_22 as eff md'; destruct dR_22 as [[(e & He & -> & ->)|(Hb & -> & ->)] ->] | intro dR_22; dand4 dR_22 as eff md' [(e & He & -> & ->)|(Hb & -> & ->)] -> | intros (eff & md' & [(e & He & -> & ->)|(Hb & -> & ->)] & ->) ])); [left; exists e; auto| right; auto].
  - (* [comment removed for export] *)
    (first [ dand5 HA as Hsvc H10 H11 H12 H13 | destruct HA as (Hsvc & H10 & H11 & H12 & H13) ]). exists (Z_to_bv 64 216). split; [exact Hsvc|]. intros o.
    (first [ dand5 HS as -> Hal Hnz Hoz Hsrc | destruct HS as (-> & Hal & Hnz & Hoz & Hsrc) ]).
    assert (A0 : in_arg (sys_input segs ms (Z_to_bv 64 216)) 0 = w old) by (rewrite in_a0_si; exact H10).
    assert (A1 : in_arg (sys_input segs ms (Z_to_bv 64 216)) 1 = w oldlen) by (rewrite in_a1_si; exact H11).
    assert (A2 : in_arg (sys_input segs ms (Z_to_bv 64 216)) 2 = w newlen) by (rewrite in_a2_si; exact H12).
    assert (A3 : in_arg (sys_input segs ms (Z_to_bv 64 216)) 3 = w MREMAP_MAYMOVE) by (rewrite in_a3_si; exact H13).
    pose proof (mremap_outcome_acfg (w old) (w oldlen) (w newlen) (w MREMAP_MAYMOVE) (sys_input segs ms (Z_to_bv 64 216)) md o
                  ltac:(rewrite in_sysno_si; apply u64_lit; lia) A0 A1 A2 A3 Hh
                  ltac:(apply u64_lit; unfold MREMAP_MAYMOVE; lia) Hal Hnz Hoz Hsrc) as E.
    cbv zeta in E. rewrite E. cbn [nstep]. unfold rlen, wlen. split.
    + intros [[Heq ->]|[Hne [(e & He & ->)|[[Hlt ->]|[(Hlt & Hig & ->)|(Hlt & dst & Hd & ->)]]]]]; eexists _, _; (split; [|reflexivity]).
      * left. auto.
      * right. split; [exact Hne|]. left. exists e. split; [exact He | split; reflexivity].
      * right. split; [exact Hne|]. right. left. auto.
      * right. split; [exact Hne|]. right. right. left. auto.
      * right. split; [exact Hne|]. right. right. right. split; [exact Hlt|]. exists dst. auto.
    + intros (eff & md' & [(Heq & -> & ->)|[Hne [(e & He & -> & ->)|[(Hlt & -> & ->)|[(Hlt & Hig & -> & ->)|(Hlt & dst & Hd & -> & ->)]]]]] & ->).
      * left. auto.
      * right. split; [exact Hne|]. left. exists e. split; [exact He | reflexivity].
      * right. split; [exact Hne|]. right. left. auto.
      * right. split; [exact Hne|]. right. right. left. auto.
      * right. split; [exact Hne|]. right. right. right. split; [exact Hlt|]. exists dst. auto.
Qed.

(* [comment removed for export] *)
Lemma at_node_gate : forall n ms md x8,
  at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  bw_gate (sys_input segs ms x8) md -> bw_gate_n n md.
Proof.
  intros n ms md x8 HA Hsvc H. unfold bw_gate, bw_gate_n in *. destruct bw_on; [| exact I].
  unfold nbudget_refused.
  destruct n; cbn [node_input]; try reflexivity; cbn [at_node] in HA.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct HA as [Hs H10]. assert (Ex : x8 = Z_to_bv 64 214) by congruence. subst x8.
    rewrite abr_brk in H by reflexivity. rewrite abr_brk by reflexivity.
    rewrite in_a0_si, H10 in H. exact H.
  - (* [comment removed for export] *)
    destruct HA as (Hs & H10 & H11 & H12 & H13 & H14 & H15). assert (Ex : x8 = Z_to_bv 64 222) by congruence. subst x8.
    rewrite abr_mmap in H by reflexivity. rewrite abr_mmap by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, H10, H11, H12, H13 in H.
    change (in_arg (sys_input segs ms (Z_to_bv 64 222)) 4) with (areg ms 14) in H.
    change (in_arg (sys_input segs ms (Z_to_bv 64 222)) 5) with (areg ms 15) in H.
    rewrite H14, H15 in H. exact H.
  - (* [comment removed for export] *)
    destruct HA as (Hs & H10 & H11 & H12). assert (Ex : x8 = Z_to_bv 64 226) by congruence. subst x8.
    rewrite abr_mprotect in H by reflexivity. rewrite abr_mprotect by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, H10, H11, H12 in H. exact H.
  - (* [comment removed for export] *)
    destruct HA as (Hs & H10 & H11 & H12 & H13). assert (Ex : x8 = Z_to_bv 64 216) by congruence. subst x8.
    rewrite abr_mremap in H by reflexivity. rewrite abr_mremap by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, H10, H11, H12, H13 in H. exact H.
Qed.

(* [comment removed for export] *)
Theorem rz_at_node : forall n ms md T,
  at_node segs n ms -> KI md -> nsafe n md ->
  (forall eff md', nstep n md eff md' -> bw_gate_n n md -> KI md' -> realizes segs (mkCfg (nret ms eff) md') T) ->
  realizes segs (mkCfg ms md) T.
Proof.
  intros n ms md T HA HK HS HC.
  destruct HK as [Hh Hl].
  destruct (at_node_outcome n ms md HA Hh HS) as (x8 & Hsvc & Hchar).
  apply (rz_sysnode ms md x8 (nstep n md) T Hh Hl Hsvc Hchar).
  - intros eff md' Hst. exact (nstep_KI n md eff md' (conj Hh Hl) Hst).
  - apply nstep_inhabited. exact HS.
  - intros eff md' Hst Hgate. unfold nret in HC.
    apply HC; [exact Hst | exact (at_node_gate n ms md x8 HA Hsvc Hgate) |]. exact (nstep_KI n md eff md' (conj Hh Hl) Hst).
Qed.

Theorem knode_sound :
  @node_sound node segs (at_node segs) (fun n md eff md' evs => nstep n md eff md' /\ evs = [])
    (fun _ _ _ _ => False) KI nsafe.
Proof.
  constructor.
  - intros n ms HA. destruct n; cbn [at_node] in HA;
      repeat match goal with Hc : _ /\ _ |- _ => destruct Hc as [Hc _] end;
      try match type of HA with _ \/ _ => destruct HA as [HA|HA] end;
      rewrite HA; discriminate.
  - intros n ms mo evs X HA Hh HK HS Hss.
    destruct (at_node_outcome n ms mo HA Hh HS) as (x8 & Hsvc & Hchar).
    pose proof (sstep_cfg_sys_inv_acfg segs ms mo x8 evs X Hsvc Hss) as Hinv. cbv zeta in Hinv.
    destruct Hinv as [(eff & m' & evs0 & Hs & Hh' & Hm)
                     | [(eff & m' & evs0 & code & Hs & Hh' & Hk & -> & ->)
                     | [(eff & m' & evs0 & sig & Hs & Hk & -> & ->) | (Hs & -> & ->)]]].
    + destruct (proj1 (Hchar _) Hs) as (eff' & md' & Hst & Heq).
      apply Ok_inj in Heq as (-> & -> & ->).
      pose proof (nstep_KI n mo eff' md' HK Hst) as [_ Hl'].
      rewrite (materialize_model_accesses_no_lazy _ _ Hl') in Hm. destruct Hm as [-> ->].
      left. exists eff', md'. split; [reflexivity|]. split; [exact Hst | reflexivity].
    + exfalso. destruct (proj1 (Hchar _) Hs) as (eff' & md' & Hst & Heq).
      apply Ok_inj in Heq as (-> & -> & ->).
      rewrite (proj1 (nstep_KI n mo eff' md' HK Hst)) in Hh'. discriminate Hh'.
    + exfalso. destruct (proj1 (Hchar _) Hs) as (eff' & md' & Hst & Heq).
      apply Ok_inj in Heq as (-> & -> & ->).
      rewrite (m_killed_of_m_halted_none _ (proj1 (nstep_KI n mo eff' md' HK Hst))) in Hk. discriminate Hk.
    + exfalso. destruct (proj1 (Hchar _) Hs) as (eff' & md' & Hst & Heq).
      exact (Unmodeled_Ok _ _ _ Heq).
  - intros n ms mo rsp mo' evs HA Hh HK HS [Hst ->].
    destruct (nstep_KI n mo rsp mo' HK Hst) as [Hh' Hl'].
    split; [exact Hh'|]. split; [split; [exact Hh' | exact Hl']|].
    destruct (at_node_outcome n ms mo HA Hh HS) as (x8 & Hsvc & Hchar).
    apply (sstep_cfg_syscall_acfg segs ms mo x8 rsp mo' mo' []); [exact Hh | exact Hsvc | | exact Hh' |].
    + apply (proj2 (Hchar _)). exists rsp, mo'. split; [exact Hst | reflexivity].
    + apply materialize_model_accesses_no_lazy. exact Hl'.
  - intros n ms mo code mo' _ _ _ _ [].
  - intros n ms mo HA Hh HK HS. left.
    destruct (nstep_inhabited n mo HS) as (eff & md' & Hst).
    exists eff, md', []. split; [exact Hst | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.
