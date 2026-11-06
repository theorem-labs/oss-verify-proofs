(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Realloc ReallocProto RawAlloc
  KArith KInv KLink KStep KStepX MI_Tree MI_Sim LB_Kernel LB_Embed LB_Tree LB_TreeX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_mremap_source : forall old osz nsz mo rsp mo' evs,
  0 <= old -> old mod 4096 = 0 -> 0 < osz -> osz mod 4096 = 0 -> 0 < nsz -> nsz mod 4096 = 0 ->
  old + Z.max osz nsz < 2^64 ->
  nstep (NMremap old osz nsz Uapi.MREMAP_MAYMOVE) mo rsp mo' evs ->
  mremap_source_b (m_vmmaps mo) (Z_to_bv 64 old) (Z_to_bv 64 osz) osz = true.
Proof.
  intros old osz nsz mo rsp mo' evs Hold Holda Hosz Hosza Hnsz Hnsza Hhi H.
  apply nstep_mremap_iff in H. unfold check_mremap in H.
  change (bv_unsigned (Z_to_bv 64 Uapi.MREMAP_MAYMOVE)) with Uapi.MREMAP_MAYMOVE in H. cbn [Z.eqb Pos.eqb negb Uapi.MREMAP_MAYMOVE] in H.
  rewrite (unsigned_lit old) in H by lia.
  replace (old mod page_size =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Holda). cbn [negb] in H.
  rewrite (page_align_is0_false nsz Hnsz Hnsza ltac:(lia)) in H.
  rewrite (page_align_is0_false osz Hosz Hosza ltac:(lia)) in H. cbv zeta in H.
  rewrite !unsigned_lit in H by lia. rewrite !page_round_up_Z_id in H by lia.
  destruct (mremap_source_b (m_vmmaps mo) (Z_to_bv 64 old) (Z_to_bv 64 osz) osz); [reflexivity|].
  cbn [andb negb] in H. discriminate H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gm_remap_group L pbrk mo a l0 z nl : KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  gm (KInv.set_groups ((z, nl) :: g_remove a (ld_groups L)) L) = gm L - mmap_len l0 + mmap_len nl.
Proof.
  intros HK Hin. pose proof (gm_remove_group L pbrk mo a l0 HK Hin) as G.
  unfold gm in *. cbn [ld_groups ld_metas KInv.set_groups map fold_right snd] in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma li_mremap : forall L pbrk mo rsp mo' evs a ol nl x,
  KL L pbrk mo -> LI L mo -> xevent_pre L (XMremap a ol nl Realloc.MREMAP_MAYMOVE) ->
  nstep (NMremap a ol nl Realloc.MREMAP_MAYMOVE) mo rsp mo' evs ->
  dec_mremap a ol nl [] rsp = Some x ->
  LI (xevent_post L (XMremap a ol nl Realloc.MREMAP_MAYMOVE) (mremap_val a x)) mo'.
Proof.
  intros L pbrk mo rsp mo' evs a ol nl x HK HL Hpre Hst Hd.
  cbn [xevent_pre] in Hpre. destruct Hpre as (Hq & _ & (l & Hin & Hol) & Hnl & Hnla & Hne).
  rewrite round_up_pg_eq in Hol. change (page_round_up_Z l) with (mmap_len l) in Hol.
  pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  set (n := mmap_len l) in *.
  assert (Hna : n mod 4096 = 0) by (subst n; apply mmap_len_aligned).
  pose proof (mmap_len_ge l ltac:(lia)) as N1. fold n in N1.
  assert (Hnn : mmap_len nl = nl) by (apply mmap_len_of_aligned; [lia| unfold PGSZ in Hnla; exact Hnla]).
  subst ol. change Realloc.MREMAP_MAYMOVE with Uapi.MREMAP_MAYMOVE in Hst.
  pose proof (nstep_mremap_source a n nl mo rsp mo' evs ltac:(lia) ltac:(unfold PGSZ in A3; exact A3) ltac:(lia) Hna
                ltac:(lia) ltac:(unfold PGSZ in Hnla; exact Hnla) ltac:(unfold LEN_MAX in Hnl; lia) Hst) as Hsrc.
  pose proof (nstep_dec_mremap a n nl [] mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(unfold PGSZ in A3; exact A3)
                ltac:(lia) Hna ltac:(lia) ltac:(unfold PGSZ in Hnla; exact Hnla) ltac:(unfold LEN_MAX in Hnl; lia) Hsrc (Forall_nil _) Hst)
    as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  (* [comment removed for export] *)
  assert (LIVE : forall dst, vm_live_bytes (mremap_maps_next (m_vmmaps mo) (Z_to_bv 64 a) dst (Z_to_bv 64 nl))
                            = vm_live_bytes (m_vmmaps mo) - n + nl).
  { intros dst. unfold vm_live_bytes, mremap_maps_next. cbn [vm_maps]. rewrite live_bytes_cons. cbn [snd].
    rewrite (live_bytes_remove _ _ (wz n) (kl_wf _ _ _ HK)).
    2:{ unfold went in A5. exact A5. }
    rewrite (unsigned_wz n) by lia. rewrite unsigned_lit by (unfold LEN_MAX in Hnl; lia). lia. }
  assert (Herr : is_err a = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia).
  pose proof (LI_elim _ _ HL) as HL0.
  destruct x as [e| |d]; cbn [mremap_val xevent_post].
  - (* [comment removed for export] *)
    destruct Hx as (-> & -> & _). rewrite is_err_neg by (unfold ENOMEM; lia). exact HL.
  - (* [comment removed for export] *)
    rewrite Herr. apply LI_intro. rewrite BB_set_groups, (gm_remap_group L pbrk mo a l a nl HK Hin). fold n. rewrite Hnn.
    destruct Hx as [[E _]|[[_ Evm]|(_ & _ & Evm)]]; [exfalso; exact (Hne (eq_sym E))| |]; rewrite Evm, LIVE; lia.
  - (* [comment removed for export] *)
    destruct Hx as (Hlt & Hdst & Hrf & Evm).
    apply mremap_dst_ok_true in Hdst as [(D1 & D2 & D3 & D4) _].
    assert (Hd0 : is_err d = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia). rewrite Hd0.
    apply LI_intro. rewrite BB_set_groups, (gm_remap_group L pbrk mo a l d nl HK Hin). fold n. rewrite Hnn, Evm, LIVE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem xev_step_L L e G s0 : frame_ok G -> xevent_pre L e ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (xev_step e)
        (fun z s mo => xev_step_post L e G s0 z s mo /\ LI (xevent_post L e z) mo).
Proof.
  intros HG Hpre. destruct e as [e|a ol nl fl].
  - (* [comment removed for export] *)
    cbn [xev_step xevent_pre xevent_post xev_step_post xanswer_ok] in *. exact (ev_step_L L e G s0 HG Hpre).
  - intros s mo (-> & HK & HLI & HGs).
    pose proof (xev_step_spec L (XMremap a ol nl fl) G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
    pose proof Hpre as Hpre0. cbn [xevent_pre] in Hpre0. destruct Hpre0 as (_ & -> & _).
    unfold xev_step in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
    { intros rsp. destruct (dec_mremap a ol nl [] rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    destruct (dec_mremap a ol nl [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
    assert (Ez : z = mremap_val a x) by congruence. subst z.
    exact (li_mremap L (ps_brk s0) mo rsp mo' evs a ol nl x HK HLI Hpre Hst Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem xmembedL {R} B (t : MX R) : forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> xqtree B L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (xmembed t)
        (fun r s mo => exists L', xcpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  induction t as [r|e k IH]; intros Post G L s0 HG Hq.
  - cbn [xmembed]. apply mspec_ret. intros s mo (-> & HK & HL & HGs). exists L. split; [constructor|]. cbn in Hq.
    split; [exact Hq|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. auto.
  - cbn [xmembed]. cbn in Hq. destruct Hq as (Hpre & HB & Hk).
    eapply mspec_bind.
    { eapply mspec_pre; [apply (xev_step_L L e G s0 HG Hpre)|]. intros s mo (-> & HK & HL & HGs). split; [reflexivity|]. split; [exact HK|]. split; [exact HL| exact HGs]. }
    intros z. apply mspec_pointwise. intros s1 mo1 [(Hans & HK1 & HG1 & Hm & Hfa & Hso) HL1].
    eapply mspec_conseq; [apply (IH z Post G (xevent_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. repeat split; congruence.
Qed.

End RC__.
