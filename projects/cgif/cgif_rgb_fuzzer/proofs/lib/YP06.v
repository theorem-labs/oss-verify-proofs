(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap may answer -ENOMEM, so the driver's jinv is proved from junk-freedom and well-formedness over read_phase, in place of the concrete walk). *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0h YP0r YP0c YP0e YP07 YP04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* 08b1429 cause (3): munmap may answer an injected -ENOMEM, so every munmap in free has two leaves. A concrete
   walk that enumerates both leaves at every munmap is exponential in the number of frees, so the driver's jinv is
   proved without enumerating munmap leaves. The read loop is junk-free whatever the munmap answers (only enframe
   asks for junk, and a fresh mapping's slot header is known), and its leaves are well formed (malloc_wf /
   free_wf over the yields of the one shared run). Only the first malloc is walked concretely. *)
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition JF {A} (m : M A) : Prop := forall s, jfree (m s).
Lemma JF_apply {A} (m : M A) s : JF m -> jfree (m s).
Proof. intros H. apply H. Qed.
Lemma jfree_ibind {A B} (t : itree astate A) (f : A -> itree astate B) :
jfree t -> (forall a, jfree (f a)) -> jfree (ibind t f).
Proof.
induction t as [a | q s k IH | e]; intros Ht Hf; cbn in *.
- apply Hf.
- destruct q; cbn in *;
  first [ destruct Ht as [H0 H1]; split; apply IH; assumption
        | apply IH; assumption
        | exact Ht ].
- exact I.
Qed.
Lemma jfree_mbind {A B} (m : M A) (f : A -> M B) s :
jfree (m s) -> (forall a s', jfree (f a s')) -> jfree (bind m f s).
Proof. intros Hm Hf. unfold bind. apply jfree_ibind; [exact Hm|]. intros [a s']. apply Hf. Qed.
Lemma JF_bind {A B} (m : M A) (f : A -> M B) : JF m -> (forall a, JF (f a)) -> JF (bind m f).
Proof. intros Hm Hf s. apply jfree_mbind; [apply Hm|]. intros a s'. apply Hf. Qed.
Lemma JF_ret {A} (a : A) : JF (ret a). Proof. intros s. exact I. Qed.
Lemma JF_get : JF get. Proof. intros s. exact I. Qed.
Lemma JF_put s1 : JF (put s1). Proof. intros s. exact I. Qed.
Lemma JF_modify f : JF (modify f). Proof. intros s. exact I. Qed.
Lemma JF_fail {A} f : JF (@fail A f). Proof. intros s. exact I. Qed.
Lemma JF_massert b x : JF (massert b x). Proof. intros s. unfold massert. destruct b; exact I. Qed.
Lemma JF_mcheck b x : JF (mcheck b x). Proof. intros s. unfold mcheck. destruct b; exact I. Qed.
Lemma JF_ask q : (forall p, q <> KJunk p) -> JF (ask q).
Proof.
intros J s. unfold ask. destruct q; cbn; first [exact I | split; exact I | exfalso; exact (J _ eq_refl)].
Qed.
End a.
Create HintDb jf.
Ltac jfstep :=
lazymatch goal with
| |- JF (bind _ _) => apply JF_bind; [ | intros ? ]
| |- JF (ret _) => apply JF_ret
| |- JF get => apply JF_get
| |- JF (put _) => apply JF_put
| |- JF (modify _) => apply JF_modify
| |- JF (fail _) => apply JF_fail
| |- JF (massert _ _) => apply JF_massert
| |- JF (mcheck _ _) => apply JF_mcheck
| |- JF (ask _) => apply JF_ask; intros ? ?; discriminate
| |- JF (match ?x with _ => _ end) => destruct x
| |- JF (if ?x then _ else _) => destruct x
| |- JF _ => solve [auto with jf]
end.
Ltac jfgo := repeat jfstep.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma j_getm p : JF (getm p). Proof. unfold getm. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_getm : jf.
Lemma j_setm p am : JF (setm p am). Proof. unfold setm. jfgo. Qed.
#[local] Hint Resolve j_setm : jf.
Lemma j_setslot p x : JF (setslot p x). Proof. unfold setslot. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_setslot : jf.
Lemma j_get_links p : JF (get_links p). Proof. unfold get_links. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_get_links : jf.
Lemma j_set_links p a b : JF (set_links p a b). Proof. unfold set_links. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_set_links : jf.
Lemma j_set_prev p a : JF (set_prev p a). Proof. unfold set_prev. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_set_prev : jf.
Lemma j_set_next p a : JF (set_next p a). Proof. unfold set_next. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_set_next : jf.
Lemma j_get_head h : JF (get_head h). Proof. unfold get_head. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_get_head : jf.
Lemma j_set_head h v : JF (set_head h v). Proof. unfold set_head. destruct h; cbv zeta; jfgo. Qed.
#[local] Hint Resolve j_set_head : jf.
Lemma j_queue h m : JF (queue h m). Proof. unfold queue. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_queue : jf.
Lemma j_dequeue h m : JF (dequeue h m). Proof. unfold dequeue. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_dequeue : jf.
Lemma j_dequeue_head h : JF (dequeue_head h). Proof. unfold dequeue_head. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_dequeue_head : jf.
Lemma j_free_meta m : JF (free_meta m). Proof. unfold free_meta. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_free_meta : jf.
Lemma j_set_usage_of sc v : JF (set_usage_of sc v). Proof. unfold set_usage_of. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_set_usage_of : jf.
Lemma j_step_seq : JF step_seq. Proof. unfold step_seq. jfgo. Qed.
#[local] Hint Resolve j_step_seq : jf.
Lemma j_record_seq sc : JF (record_seq sc). Proof. unfold record_seq. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_record_seq : jf.
Lemma j_activate_group m : JF (activate_group m). Proof. unfold activate_group. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_activate_group : jf.
Lemma j_find_frame p : JF (find_frame p). Proof. unfold find_frame. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_find_frame : jf.
Lemma j_forget_frame g i : JF (forget_frame g i). Proof. unfold forget_frame. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_forget_frame : jf.
Lemma j_release_slot g i : JF (release_slot g i). Proof. unfold release_slot. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_release_slot : jf.
Lemma j_new_region k len : JF (new_region k len). Proof. unfold new_region. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_new_region : jf.
Lemma j_upd_region r f : JF (upd_region r f). Proof. unfold upd_region. jfgo. Qed.
#[local] Hint Resolve j_upd_region : jf.
Lemma j_area_from_brk : JF area_from_brk. Proof. unfold area_from_brk. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_area_from_brk : jf.
Lemma j_area_from_mmap : JF area_from_mmap. Proof. unfold area_from_mmap. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_area_from_mmap : jf.
Lemma j_open_area nu : JF (open_area nu). Proof. unfold open_area. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_open_area : jf.
Lemma j_alloc_meta : JF alloc_meta. Proof. unfold alloc_meta. cbv zeta. jfgo. Qed.
#[local] Hint Resolve j_alloc_meta : jf.
Lemma j_nontrivial_free : forall fuel g i, JF (nontrivial_free fuel g i).
Proof.
induction fuel as [|f IH]; intros g i; cbn [nontrivial_free]; [apply JF_fail|].
unfold okay_to_free. cbv zeta. jfgo.
Qed.
#[local] Hint Resolve j_nontrivial_free : jf.
(* free asks only for KMunmap: it is junk-free whatever the munmap answers. *)
Lemma j_free p : JF (free p).
Proof. unfold free. destruct p as [p|]; [|apply JF_ret]. cbv zeta. jfgo. Qed.
Lemma bind_getm_hit {B} g am (f : ameta -> M B) s :
mlookup (st_metas s) g = Some (MUsed am) -> bind (getm g) f s = f am s.
Proof. intros H. unfold getm. unfold bind, get, ret. cbn [ibind]. rewrite H. cbn [ibind]. reflexivity. Qed.
(* enframe asks for junk only when the slot's header is unknown. *)
Lemma jf_enframe_hit g idx n ctr k s am :
mlookup (st_metas s) g = Some (MUsed am) -> (exists h, ss_hdr (nth_slot am idx) = Some h) ->
jfree (enframe g idx n ctr k s).
Proof.
intros Hm [h Hh]. unfold enframe. cbv zeta. rewrite (bind_getm_hit g am _ s Hm). cbv beta.
rewrite Hh. destruct h as [h3 h16]. cbv beta iota.
apply JF_apply. jfgo.
Qed.
(* A large malloc: a fresh mapping with one slot whose header is known, so enframe asks no junk. *)
Lemma jf_malloc_big n s : MMAP_THRESHOLD <= n < 2 ^ 62 -> jfree (malloc n s).
Proof.
intros Hn. unfold malloc, size_overflows.
rewrite (proj2 (Z.leb_gt (2 ^ 63 - 4096) n)) by lia.
rewrite (proj2 (Z.leb_le MMAP_THRESHOLD n)) by lia.
cbv zeta.
apply jfree_mbind; [apply JF_apply, JF_ask; intros p0 Hp0; discriminate|].
intros ok s1. destruct ok; cbn [negb]; [|exact I].
apply jfree_mbind; [apply JF_apply, j_new_region|]. intros r s2.
apply jfree_mbind; [apply JF_apply, j_step_seq|]. intros [] s3.
apply jfree_mbind; [apply JF_apply, j_alloc_meta|]. intros og s4.
destruct og as [g|]; cbv beta iota.
- cbn [bind setm modify get put ret ibind].
  apply jfree_ibind; [| intros [a s']; exact I].
  eapply jf_enframe_hit.
  + cbn [st_metas set_mmap_counter set_metas]. apply mlookup_mupdate_same.
  + eexists. reflexivity.
- match goal with |- jfree (?m ?s) => apply (JF_apply m s) end. jfgo.
Qed.
Lemma jf_read_phase : forall f L cap buf s, CAP0 <= cap -> jfree (read_phase f L cap buf s).
Proof.
induction f as [|f IH]; intros L cap buf s Hcap; cbn [read_phase]; [exact I|].
destruct (L <? cap); [exact I|].
destruct (MAX_INPUT <=? cap) eqn:EM; [exact I|].
apply Z.leb_gt in EM. unfold MAX_INPUT in EM.
apply jfree_mbind; [apply jf_malloc_big; unfold MMAP_THRESHOLD, CAP0 in *; lia|].
intros [nb|] s1; cbv beta iota; [|exact I].
apply jfree_mbind; [apply JF_apply, (j_free (Some buf))|].
intros [] s2. apply IH. unfold CAP0 in *. lia.
Qed.
Lemma cpath_ibind_inv {A B} : forall (t : itree astate A) (f : A -> itree astate B) tr b,
cpath (ibind t f) tr b -> exists tr1 tr2 a, cpath t tr1 a /\ cpath (f a) tr2 b.
Proof.
induction t as [a | q s k IH | e]; intros f tr b H; cbn in H.
- exists [], tr, a. split; [reflexivity | exact H].
- destruct tr as [|[q' z] tr']; [destruct H|]. destruct H as (Eq & Hc & H).
  destruct (IH z f tr' b H) as (tr1 & tr2 & a & H1 & H2).
  exists ((q', z) :: tr1), tr2, a. split; [cbn; repeat split; assumption | exact H2].
- destruct tr; destruct H.
Qed.
Lemma cpath_mbind_inv {A B} (m : M A) (f : A -> M B) s tr b :
cpath (bind m f s) tr b -> exists tr1 tr2 a s1, cpath (m s) tr1 (a, s1) /\ cpath (f a s1) tr2 b.
Proof.
intros H. unfold bind in H. destruct (cpath_ibind_inv _ _ _ _ H) as (tr1 & tr2 & [a s1] & H1 & H2).
exists tr1, tr2, a, s1. split; [exact H1 | exact H2].
Qed.
Lemma cpath_ret_inv {A} (a : A) s tr r s' : cpath (ret a s) tr (r, s') -> s' = s.
Proof. unfold ret. destruct tr; cbn; [intros H; injection H as _ E; symmetry; exact E | intros []]. Qed.
(* Every state the read loop ends in is well formed, whatever the munmap answers. *)
Lemma rp_wf : forall f L cap buf s tr r s2,
WF s -> In (buf, cap) (user_blocks s) -> 0 <= cap ->
cpath (read_phase f L cap buf s) tr (r, s2) -> WF s2.
Proof.
induction f as [|f IH]; intros L cap buf s tr r s2 HW Hin Hcap H; cbn [read_phase] in H.
- rewrite (cpath_ret_inv _ _ _ _ _ H). exact HW.
- destruct (L <? cap); cbv iota in H; [rewrite (cpath_ret_inv _ _ _ _ _ H); exact HW|].
  destruct (MAX_INPUT <=? cap); cbv iota in H; [rewrite (cpath_ret_inv _ _ _ _ _ H); exact HW|].
  apply cpath_mbind_inv in H as (tr1 & tr2 & p & s1 & H1 & H2).
  pose proof (malloc_wf s (2 * cap) tr1 p s1 HW ltac:(lia) (cpath_yields _ _ _ H1)) as HW1.
  pose proof (malloc_blocks s (2 * cap) tr1 p s1 HW ltac:(lia) (cpath_yields _ _ _ H1)) as HB1.
  destruct p as [nb|]; cbv beta iota in H2.
  + destruct HB1 as (l1 & l2 & E1 & E2 & _ & Hnew).
    apply cpath_mbind_inv in H2 as (tr3 & tr4 & u & s3 & H3 & H4). destruct u.
    assert (Hbuf1 : In (buf, cap) (user_blocks s1)).
    { rewrite E1. rewrite E2 in Hin. apply in_app_iff in Hin as [Hx|Hx]; apply in_app_iff;
      [left; exact Hx | right; right; exact Hx]. }
    pose proof (free_wf s1 buf cap tr3 s3 HW1 Hbuf1 (cpath_yields _ _ _ H3)) as HW3.
    destruct (free_blocks s1 buf cap tr3 s3 HW1 Hbuf1 (cpath_yields _ _ _ H3)) as (m1 & m2 & F1 & F2).
    assert (Hnb3 : In (nb, 2 * cap) (user_blocks s3)).
    { assert (Hnb1 : In (nb, 2 * cap) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
      rewrite F1 in Hnb1. rewrite F2.
      apply in_app_iff in Hnb1 as [Hx|[Hx|Hx]]; apply in_app_iff; [left; exact Hx | | right; exact Hx].
      exfalso. injection Hx as Ex _. apply Hnew. apply in_map_iff. exists (buf, cap). split; [exact Ex | exact Hin]. }
    exact (IH L (2 * cap) nb s3 tr4 r s2 HW3 Hnb3 ltac:(lia) H4).
  + rewrite (cpath_ret_inv _ _ _ _ _ H2). exact HW1.
Qed.
End b.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem do_jinv_proved : forall data fs, jinv (leaf_shape data fs) (driver_tree data).
Proof.
intros data fs. unfold driver_tree, driver_m.
apply jinv_mbind.
- apply jfree_jinv. vm_compute. repeat split.
- intros tr p0 s1 Hp.
  pose proof (malloc_wf init_state CAP0 tr p0 s1 wf_init ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hp)) as HW1.
  pose proof (malloc_blocks init_state CAP0 tr p0 s1 wf_init ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hp)) as HB1.
  destruct p0 as [b0|]; cbv beta iota; [|exact I].
  destruct HB1 as (l1 & l2 & E1 & _).
  assert (Hb0 : In (b0, CAP0) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
  apply jinv_mbind.
  + apply jfree_jinv. apply jf_read_phase. unfold CAP0; lia.
  + intros tr2 r s2 Hp2.
    pose proof (rp_wf READ_FUEL (dlen data) CAP0 b0 s1 tr2 r s2 HW1 Hb0 ltac:(unfold CAP0; lia) Hp2) as HW2.
    destruct r as [| |buf cap]; cbv beta iota; [exact I | exact I |].
    destruct (dlen data <? HDR_MIN) eqn:?; [exact I|].
    destruct (dlen data <? HDR_MIN + config_len data) eqn:?; [exact I|].
    destruct (payload_len data =? 0) eqn:?; [exact I|].
    apply jinv_mbind.
    * eapply jinv_malloc_nonesome;
      [ exact HW2
      | unfold payload_len, HDR_MIN, config_len, dlen in *; bool_hyps; lia
      | intros; cbv beta iota; cbn [tset ret fst snd leaf_shape]; apply t_eq_refl
      | intros; cbv beta iota; cbn [tset ret fst snd leaf_shape]; apply t_eq_refl ].
    * intros ? [?|] ? ?; cbv beta iota; exact I.
Qed.
End c.
