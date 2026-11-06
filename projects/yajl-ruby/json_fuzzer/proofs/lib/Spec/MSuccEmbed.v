(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat NodesCfg Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe STree Malloc RawAlloc KArith KInv KLink KStep KLive KArena
  LB_Kernel LB_Embed KLiveCfg MSucc MLen MSuccTall Realloc ReallocProto KStepX LB_TreeX LB_EmbedX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition vmc (mo : Model) : list (word * word) * Z := (vm_reserved (m_vmmaps mo), vm_limit (m_vmmaps mo)).

Lemma vmc_nstep n mo rsp mo' evs : nstep n mo rsp mo' evs -> vmc mo' = vmc mo.
Proof. intros H. destruct (nstep_vm_consts _ _ _ _ _ H) as (E1 & E2 & _). unfold vmc. rewrite E1, E2. reflexivity. Qed.

Lemma ctall_vmc {A} (t : itree node (exc A)) : forall mo v, vmc mo = v -> ctall t mo (fun _ mo' => vmc mo' = v).
Proof.
  unfold ctall. induction t as [r | n k IH]; intros mo v Hv; cbn; [destruct r; auto|].
  intros rsp mo' evs Hst. apply IH. rewrite <- Hv. eapply vmc_nstep. eapply nstep_cfg_sub. exact Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EMBED.
(* [comment removed for export] *)
Variables (B LENB RCMAX VMIN : Z).
Hypothesis HB0 : 0 <= B.
Hypothesis HLENB : 0 < LENB /\ LENB mod 4096 = 0.
Hypothesis HNUM : LENB * (B / PGSZ + RCMAX + 1) <= alloc_ceiling - PGSZ.
Hypothesis HVM : B + LENB <= VMIN.

(* [comment removed for export] *)
Variable v : list (word * word) * Z.
Hypothesis Hv : rcost (fst v) <= RCMAX /\ VMIN <= snd v.

(* [comment removed for export] *)

Lemma mmap_len_le_LENB len : 0 < len -> len <= LENB -> mmap_len len <= LENB.
Proof.
  intros H1 H2. destruct HLENB as [L1 L2]. pose proof (mmap_len_ge len H1) as [M1 M2]. pose proof (mmap_len_aligned len) as M3.
  destruct (Z.le_gt_cases (mmap_len len) LENB) as [|Hgt]; [assumption| exfalso].
  pose proof (lt_aligned LENB (mmap_len len) 4096 ltac:(lia) L2 M3 Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma room_at mo len : vmc mo = v -> live_bytes (vm_maps (m_vmmaps mo)) <= B -> 0 < len -> len <= LENB -> MMAP_ROOM mo len.
Proof.
  intros Hmo HL H1 H2. destruct Hv as [R1 R2]. unfold vmc in Hmo.
  assert (E1 : vm_reserved (m_vmmaps mo) = fst v) by (rewrite <- Hmo; reflexivity).
  assert (E2 : vm_limit (m_vmmaps mo) = snd v) by (rewrite <- Hmo; reflexivity).
  pose proof (mmap_len_le_LENB len H1 H2) as ML. pose proof (mmap_len_ge len H1) as [M1 _].
  pose proof (live_bytes_nonneg (vm_maps (m_vmmaps mo))) as LV0. pose proof (rcost_nonneg (vm_reserved (m_vmmaps mo))) as RC0.
  split.
  - rewrite E1 in *. etransitivity; [| exact HNUM].
    etransitivity; [apply Z.mul_le_mono_nonneg_r; [| exact ML]|].
    { pose proof (Z.div_pos (live_bytes (vm_maps (m_vmmaps mo))) PGSZ LV0 ltac:(unfold PGSZ; lia)). lia. }
    apply Z.mul_le_mono_nonneg_l; [lia|].
    pose proof (Z.div_le_mono (live_bytes (vm_maps (m_vmmaps mo))) B PGSZ ltac:(unfold PGSZ; lia) HL). lia.
  - rewrite E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctall_msys_ret {A C} n (dec : resp -> option A) (f : A -> C) (s : PState) mo (Q : C -> Prop) :
  (forall rsp mo' evs a, nstep_cfg acfg n mo rsp mo' evs -> dec rsp = Some a -> Q (f a)) ->
  ctall ((a <- msys n dec ;; mret (f a)) s) mo (fun p _ => Q (fst p)).
Proof.
  intros H. unfold ctall, mbind, msys, mret, enode, ebind. cbn.
  intros rsp mo' evs Hst. destruct (dec rsp) as [a|] eqn:E; cbn; [| exact I].
  eapply H; [exact Hst | exact E].
Qed.

Lemma ev_step_adm_cfg L e s0 mo :
  event_pre L e -> KL L (ps_brk s0) mo -> LI L mo -> gm L + BB L <= B -> vmc mo = v ->
  ev_len_ok LENB e ->
  ctall (ev_step e s0) mo (fun p _ => ev_adm e (fst p)).
Proof.
  intros Hpre HK HLI HBL Hmo Hlen.
  pose proof (LI_elim _ _ HLI) as LV. unfold vm_live_bytes in LV.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - (* [comment removed for export] *) unfold ctall. apply tall_trivial. intros [|?] ?; exact I.
  - (* [comment removed for export] *)
    destruct Hpre as [(Hq & -> & -> & Hprot & Hrange)|(cur & Hph & -> & -> & -> & ->)].
    + cbn [ev_len_ok] in Hlen. change (map_fixed_b MAPF) with false in Hlen.
      destruct Hlen as [Hlen|Hlen]; [discriminate|].
      pose proof (room_at mo len Hmo ltac:(lia) ltac:(lia) Hlen) as ROOM.
      unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
      destruct Hprot as [-> | ->].
      * change (PROT_NONE =? 0) with true. cbv iota.
        apply ctall_msys_ret. intros rsp mo' evs a Hst Hd. cbn [ev_adm]. intros _.
        destruct (nstep_cfg_mmap_none_granted L (ps_brk s0) mo len rsp mo' evs HK Hrange ROOM Hst) as (x & Hx & He).
        rewrite Hx in Hd. injection Hd as <-. exact He.
      * change (PROT_RW =? 0) with false. cbv iota.
        apply ctall_msys_ret. intros rsp mo' evs a Hst Hd. cbn [ev_adm]. intros _.
        destruct (nstep_cfg_mmap_rw_granted L (ps_brk s0) mo len rsp mo' evs HK Hrange ROOM Hst) as (x & Hx & He).
        rewrite Hx in Hd. injection Hd as <-. exact He.
    + (* [comment removed for export] *)
      unfold ctall. apply tall_trivial. intros [|[z s']] ?; cbn; [exact I|]. intros Hf. exfalso.
      revert Hf. change (map_fixed_b MAPFX) with true. discriminate.
  - (* [comment removed for export] *) unfold ctall. apply tall_trivial. intros [|?] ?; exact I.
  - (* [comment removed for export] *)
    destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk).
    unfold ev_step. apply ctall_msys_ret. intros rsp mo' evs a Hst Hd. cbn [ev_adm].
    assert (Hbud : live_bytes (vm_maps (m_vmmaps mo)) + PGSZ <= vm_limit (m_vmmaps mo)).
    { destruct Hv as [_ R2]. unfold vmc in Hmo. assert (E2 : vm_limit (m_vmmaps mo) = snd v) by (rewrite <- Hmo; reflexivity).
      rewrite E2. destruct HLENB. pose proof (lt_aligned 0 LENB 4096 ltac:(lia) eq_refl ltac:(assumption) ltac:(lia)). unfold PGSZ. lia. }
    rewrite (nstep_cfg_mprotect_granted L (ps_brk s0) mo b l k rsp mo' evs HK Hq Hin Hk Hbud Hst) in Hd.
    injection Hd as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem membed_cfg {R} (t : stree ev Z R) : forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0 mo (P : R -> Prop),
  frame_ok G -> qtree B L t Post -> lok LENB TrueP t -> sok P t ->
  KL L (ps_brk s0) mo -> LI L mo -> G s0 mo -> gm L + BB L <= B -> vmc mo = v ->
  ctall (membed t s0) mo (fun p _ => P (fst p)).
Proof.
  induction t as [r | e k IH]; intros Post G L s0 mo P HG Hq Hl Hs HK HLI HGs HBL Hmo.
  - cbn in Hs. unfold ctall. cbn. exact Hs.
  - cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HBD & Hk).
    (* [comment removed for export] *)
    assert (Hl' : ev_len_ok LENB e /\ forall z, lok LENB TrueP (k z)).
    { destruct e; cbn in Hl, Hpre; try exact Hl; contradiction. }
    destruct Hl' as [Hlen Hlk].
    assert (Hsk : forall z, ev_adm e z -> sok P (k z)).
    { destruct e; cbn in Hs, Hpre; try exact Hs; contradiction. }
    (* [comment removed for export] *)
    pose proof (ev_step_L L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK (conj HLI HGs)))) as F1.
    apply ctall_of_etwf in F1.
    pose proof (ev_step_adm_cfg L e s0 mo Hpre HK HLI HBL Hmo Hlen) as F2.
    pose proof (ctall_vmc (ev_step e s0) mo v Hmo) as F3.
    pose proof (ctall_conj _ _ _ _ F1 (ctall_conj _ _ _ _ F2 F3)) as F. clear F1 F2 F3.
    unfold mbind. apply ctall_ebind. eapply ctall_mono; [exact F|].
    intros [z s1] mo1 ([(Hans & HK1 & HG1 & Hm & Hfa & Hso) HLI1] & Hadm & Hv1). cbn [fst snd] in *.
    apply (IH z Post G (event_post L e z) s1 mo1 P HG).
    + apply Hk. exact Hans.
    + apply Hlk.
    + apply Hsk. exact Hadm.
    + exact HK1.
    + exact HLI1.
    + exact HG1.
    + apply HBD. exact Hans.
    + exact Hv1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition xev_adm (e : xev) (z : Z) : Prop :=
  match e with XE e => ev_adm e z | XMremap _ _ _ _ => True end.
Definition xev_len_ok (LENB : Z) (e : xev) : Prop :=
  match e with XE e => ev_len_ok LENB e | XMremap _ _ _ _ => True end.

Lemma xsok_vis_inv {R} (P : R -> Prop) e (k : Z -> MX R) :
  xsok P (SVis e k) -> match e with XE (EUndef _) => True | _ => forall z, xev_adm e z -> xsok P (k z) end.
Proof. intros H. destruct e as [e|]; [destruct e|]; cbn in *; auto. Qed.

Lemma xlok_vis_inv {R} (P : R -> Prop) e (k : Z -> MX R) :
  xlok LENB P (SVis e k) -> match e with XE (EUndef _) => True | _ => xev_len_ok LENB e /\ forall z, xlok LENB P (k z) end.
Proof. intros H. destruct e as [e|]; [destruct e|]; cbn in *; auto. Qed.

Lemma xev_step_adm_cfg L e s0 mo :
  xevent_pre L e -> KL L (ps_brk s0) mo -> LI L mo -> gm L + BB L <= B -> vmc mo = v ->
  xev_len_ok LENB e ->
  ctall (xev_step e s0) mo (fun p _ => xev_adm e (fst p)).
Proof.
  intros Hpre HK HLI HBL Hmo Hlen. destruct e as [e|a ol nl fl]; cbn [xev_step xevent_pre xev_len_ok xev_adm] in *.
  - apply (ev_step_adm_cfg L); assumption.
  - unfold ctall. apply tall_trivial. intros [|?] ?; exact I.
Qed.

Theorem xmembed_cfg {R} (t : MX R) : forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0 mo (P : R -> Prop),
  frame_ok G -> xqtree B L t Post -> xlok LENB TrueP t -> xsok P t ->
  KL L (ps_brk s0) mo -> LI L mo -> G s0 mo -> gm L + BB L <= B -> vmc mo = v ->
  ctall (xmembed t s0) mo (fun p _ => P (fst p)).
Proof.
  induction t as [r | e k IH]; intros Post G L s0 mo P HG Hq Hl Hs HK HLI HGs HBL Hmo.
  - cbn in Hs. unfold ctall. cbn. exact Hs.
  - cbn [xmembed]. cbn in Hq. destruct Hq as (Hpre & HBD & Hk).
    assert (Hl' : xev_len_ok LENB e /\ forall z, xlok LENB TrueP (k z)).
    { destruct e as [e|]; [destruct e|]; cbn in Hl, Hpre; try exact Hl; try contradiction. split; [exact I| exact Hl]. }
    destruct Hl' as [Hlen Hlk].
    assert (Hsk : forall z, xev_adm e z -> xsok P (k z)).
    { destruct e as [e|]; [destruct e|]; cbn in Hs, Hpre; try exact Hs; try contradiction. intros z _. exact (Hs z). }
    pose proof (xev_step_L L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK (conj HLI HGs)))) as F1.
    apply ctall_of_etwf in F1.
    pose proof (xev_step_adm_cfg L e s0 mo Hpre HK HLI HBL Hmo Hlen) as F2.
    pose proof (ctall_vmc (xev_step e s0) mo v Hmo) as F3.
    pose proof (ctall_conj _ _ _ _ F1 (ctall_conj _ _ _ _ F2 F3)) as F. clear F1 F2 F3.
    unfold mbind. apply ctall_ebind. eapply ctall_mono; [exact F|].
    intros [z s1] mo1 ([(Hans & HK1 & HG1 & Hm & Hfa & Hso) HLI1] & Hadm & Hv1). cbn [fst snd] in *.
    apply (IH z Post G (xevent_post L e z) s1 mo1 P HG).
    + apply Hk. exact Hans.
    + apply Hlk.
    + apply Hsk. exact Hadm.
    + exact HK1.
    + exact HLI1.
    + exact HG1.
    + apply HBD. exact Hans.
    + exact Hv1.
Qed.

End EMBED.
End RC__.
