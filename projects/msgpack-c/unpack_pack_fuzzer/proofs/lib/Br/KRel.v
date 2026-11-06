(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import ITree Nodes NodesM Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KOwn A_MallocBlocks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Contracts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition GT : PState -> Model -> Prop := fun _ _ => True.

Lemma frame_ok_GT : frame_ok GT.
Proof. intros s s' mo mo' _ _ _ _. exact I. Qed.

Definition KREL (s : PState) (LB : list block) (mo : Model) : Prop :=
  OWNS (map blk_id LB) GT s mo.

Lemma KREL_OWN : forall s LB mo, KREL s LB mo <-> OWNS (map blk_id LB) GT s mo.
Proof. intros; unfold KREL; reflexivity. Qed.

Lemma map_blk_id_cons : forall p A n LB, map blk_id ((p, A, n) :: LB) = p :: map blk_id LB.
Proof. reflexivity. Qed.

Lemma KREL_frame : forall s LB mo mo',
  m_vm mo' = m_vm mo -> m_halted mo' = None -> KREL s LB mo -> KREL s LB mo'.
Proof.
  intros s LB mo mo' Hvm Hh [(L & Hc & HK & Hi) [Hnd _]].
  split; [| split; [exact Hnd | exact I]].
  exists L. split; [exact Hc|]. split; [| exact Hi].
  assert (Evm : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite Hvm; reflexivity).
  eapply KL_vm_eq; [exact HK | | exact Hh | rewrite Evm; reflexivity ..].
  pose proof (kl_minv _ _ _ HK) as Hmi. unfold minv, m_vm_lazy in *. rewrite Hvm. exact Hmi.
Qed.

Lemma KREL_perm : forall s LB LB' mo, Permutation LB LB' -> KREL s LB mo -> KREL s LB' mo.
Proof. intros s LB LB' mo HP H. unfold KREL in *. eapply OWNS_perm; [apply Permutation_map; exact HP | exact H]. Qed.

Lemma KREL_ext : forall s s' LB mo, ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> KREL s LB mo -> KREL s' LB mo.
Proof. intros s s' LB mo H1 H2 H. unfold KREL in *. eapply OWNS_other; [exact H | exact H1 | exact H2 | exact I]. Qed.

Lemma KREL_nodup : forall s LB mo, KREL s LB mo -> List.NoDup (map blk_slot LB).
Proof.
  intros s LB mo [_ [Hnd _]]. rewrite map_map in Hnd. exact Hnd.
Qed.

Lemma KREL_nodup_id : forall s LB mo, KREL s LB mo -> List.NoDup (map blk_id LB).
Proof.
  intros s LB mo [_ [Hnd _]]. eapply NoDup_map_inv. exact Hnd.
Qed.

Lemma KREL_halted : forall s LB mo, KREL s LB mo -> m_halted mo = None.
Proof. intros s LB mo [(L & _ & HK & _) _]. exact (kl_halt _ _ _ HK). Qed.

Definition mtr_malloc (s : PState) (n : Z) (r : option bptr) (s' : PState) : Prop :=
  exists L L', MI_Contracts.SIMREL (ps_m s) L /\ cpath L (cmalloc (ps_m s) n) L' (ps_m s', option_map fst r).

Definition mtr_free (s : PState) (p : bptr) (s' : PState) : Prop :=
  exists L L', MI_Contracts.SIMREL (ps_m s) L /\ In (fst p) (ld_live L) /\ cpath L (cfree (ps_m s) (Some (fst p))) L' (ps_m s').

Lemma raw_malloc_spec_cp : forall X n s0, 0 <= n ->
  mspec (fun s mo => s = s0 /\ OWNS X GT s mo) (raw_malloc n)
        (fun r s mo => match r with
                       | Some p => OWNS (p :: X) GT s mo /\ n < 2^63
                       | None => OWNS X GT s mo
                       end /\ mtr_malloc s0 n r s).
Proof.
  intros X n s0 Hn. unfold raw_malloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0'.
  apply mspec_pointwise. intros s1 mo1 [-> [-> [(L & Hc & HK & Hi) [Hnd HGs]]]].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s0) n) _ GT L s0 frame_ok_GT (MI_Contracts.cmalloc_contract_sim _ _ _ Hc Hn))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  assert (Hcr : MI_Contracts.SIMREL st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
  { exact (MI_Contracts.sim_malloc_step _ _ _ _ _ _ Hc Hn Hp). }
  assert (MTR : forall r : option bptr, option_map fst r = p -> mtr_malloc s0 n r (set_m st' s2)).
  { intros r Hr. exists L, L'. split; [exact Hc|]. cbn [set_m ps_m]. rewrite Hr. exact Hp. }
  destruct p as [c|].
  - split; [| apply MTR; reflexivity]. split.
    + split; [|split; [|exact I]].
      * exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
        cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
      * cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
    + destruct (size_overflows n) eqn:E.
      * exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
      * unfold size_overflows in E. apply Z.leb_gt in E. lia.
  - split; [| apply MTR; reflexivity]. split; [|split; [exact Hnd| exact I]].
    exists L'. split; [exact Hcr|]. split; [exact HK'|]. rewrite Hlive. exact Hi.
Qed.

Lemma raw_free_spec_cp : forall X p s0,
  mspec (fun s mo => s = s0 /\ OWNS (p :: X) GT s mo) (raw_free p) (fun _ s mo => OWNS X GT s mo /\ mtr_free s0 p s).
Proof.
  intros X p s0. unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s0'.
  apply mspec_pointwise. intros s1 mo1 [-> [-> [(L & Hc & HK & Hi) [Hnd HGs]]]].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cfree (ps_m s0) (Some (fst p))) _ GT L s0 frame_ok_GT (MI_Contracts.cfree_contract_sim _ _ _ Hc Hin))|].
    intros s mo [-> ->]. auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & _ & HK' & HG' & Hm & Hfa & Hso).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->].
  assert (Hcr : MI_Contracts.SIMREL st' (set_live (ap_remove (fst p) (ld_live L')) L')).
  { exact (MI_Contracts.sim_free_step _ _ _ _ _ Hc Hin Hp). }
  split.
  - split; [|split; [inversion Hnd; assumption| exact I]].
    exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
    cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
    + apply Hi. right. exact Hx.
    + inversion Hnd; subst. intros ->. apply H1. exact Hx.
  - exists L, L'. split; [exact Hc|]. split; [exact Hin|]. cbn [set_m ps_m]. exact Hp.
Qed.

Lemma raw_malloc_spec_K : forall LB n s0, 0 <= n ->
  mspec (fun s mo => s = s0 /\ KREL s LB mo) (raw_malloc n)
        (fun r s mo => match r with
                       | Some p => (forall A, KREL s ((p, A, n) :: LB) mo)
                       | None => KREL s LB mo
                       end /\ mtr_malloc s0 n r s).
Proof.
  intros LB n s0 Hn. eapply mspec_post; [apply (raw_malloc_spec_cp (map blk_id LB) n s0 Hn)|].
  intros [p|] s mo [H M]; cbn beta iota in *; split; try exact M.
  - intros A. unfold KREL. rewrite map_blk_id_cons. exact (proj1 H).
  - exact H.
Qed.

End CEIL.
