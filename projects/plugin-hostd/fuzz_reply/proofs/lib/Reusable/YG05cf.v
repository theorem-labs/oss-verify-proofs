(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG05cf.v, sha256 ffa25e2673326a09f5ab2584a1a110bcd915a94677198800731509aabb10a996.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.
   Plus the P'' (Univ trace carrier) delta of commit 94ab015e127b for cgif/cgif_file_fuzzer/lib/YG05cf.v, taken 3-way (base d94d29d53c8). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the fake-stack laws.
   cgif's YG05.v (stack_malloc_progress :70, Wf_push_frame :86, stack_malloc_ok :99, stack_free_ok :127)
   restated over Wf_cf (YG01cf.v). The state-only lemmas of YG05.v (fs_probe_some, fs_probe_none,
   count_cid_ge, mod_window_nodup, mem_pos_spec, mem_pos_false, del_pos_spec, BigInv_set_fs) do not mention
   Wf, so they are used from YG05.v as they are.
   NOT restated here:
   - model_laws_ok (YG05.v:139): its record model_laws (YG0d.v:514) takes `st_nev s < EV_MAX` in ml_malloc /
     ml_free. Its cf form, the record model_laws_cf and its assembly model_laws_cf_of_free, is in YG0ucf.v,
     beside malloc_cf's law, and uses the stack laws below.
   - regime_big_set_fs and regime_ok_small (YG05.v:154-157): they are about the event regime, which the cf
     instance does not have.
   cgif's YG05.v is NOT edited. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

Section STACKCF.
Context {cp : CfParams}.

(* cgif's stack_malloc_post / stack_free_post (YG01.v:462-474) with Wf_cf for Wf. *)
Definition stack_malloc_post_cf (U : Univ) (s : astate) (cid : Z) (ns : bool) (r : sptr * astate) : Prop :=
let (p, s') := r in
Wf_cf U s' /\ (exists f, s' = set_fs f s) /\
match p with
| PFake c pos => c = cid /\ 0 <= pos < fs_frames cid /\ frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s)
| PNull => s' = s
| _ => False
end.

Definition stack_free_post_cf (U : Univ) (s : astate) (cid pos : Z) : Prop :=
Wf_cf U (stack_free_state cid pos s) /\
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.

(* set_fs touches only st_fs, so every field but wfc_fakestack carries over: by conversion, except the
   two records indexed by the state itself (wf_quar, wf_sec_cf), which go through their _ext lemmas. *)
Lemma WfP_cf_set_fs : forall U pp cc bb s f,
WfP_cf U pp cc bb s -> wf_fs (set_fs f s) -> WfP_cf U pp cc bb (set_fs f s).
Proof.
intros U pp cc bb s f W F. destruct W. constructor; try assumption.
- apply (wf_quar_ext s); [reflexivity | reflexivity | reflexivity | assumption].
- apply (wf_sec_cf_ext s); [reflexivity | reflexivity | reflexivity | reflexivity | assumption].
Qed.

Theorem stack_malloc_progress_cf : forall U s cid,
Wf_cf U s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s').
Proof.
intros U s cid W Hc Hcnt. pose proof (fs_frames_pos cid Hc) as HN.
unfold stack_malloc, bind, get, put, ret. cbn [ibind].
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs s)) cid (znth 0 cid (fs_hint (st_fs s)))) as [[pos hint']|] eqn:EP.
- cbn [ibind]. exists pos. eexists. reflexivity.
- exfalso. set (N := fs_frames cid) in *. set (hint := znth 0 cid (fs_hint (st_fs s))) in *.
pose proof (fs_probe_none _ _ _ _ EP) as ALL.
pose proof (count_cid_ge cid (fs_live (st_fs s)) (map (fun j => (hint + Z.of_nat j) mod N) (seq 0 (Z.to_nat N)))
(mod_window_nodup N hint (Z.to_nat N) HN ltac:(lia))) as GE.
rewrite length_map, length_seq in GE. unfold frames in Hcnt.
specialize (GE ltac:(apply Forall_forall; intros p Hp; apply in_map_iff in Hp as (j & <- & Hj); apply in_seq in Hj;
apply mem_pos_spec; apply ALL; lia)). lia.
Qed.

Lemma Wf_cf_push_frame : forall U s cid pos hint',
Wf_cf U s -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> 0 <= hint' -> ~ In (cid, pos) (frames s) ->
Wf_cf U (set_fs (mkFS (zupd cid hint' (fs_hint (st_fs s))) ((cid, pos) :: fs_live (st_fs s))) s).
Proof.
intros U s cid pos hint' W Hc Hpos Hh Hni. unfold Wf_cf in *. apply WfP_cf_set_fs; [exact W|].
destruct (wfc_fakestack _ _ _ _ _ W) as [[L F] ND LV]. constructor; cbn [st_fs set_fs fs_hint fs_live].
- split; [rewrite zupd_length; exact L|]. unfold zupd.
apply Forall_nth. intros i d Hi. rewrite lupd_length in Hi. destruct (Nat.eq_dec i (Z.to_nat cid)) as [->|Hne].
+ rewrite nth_lupd_same by lia. exact Hh.
+ rewrite nth_lupd_other by (intros E; apply Hne; symmetry; exact E). exact (proj1 (Forall_nth _ _) F i d Hi).
- constructor; [exact Hni | exact ND].
- constructor; [cbn; lia | exact LV].
Qed.

Theorem stack_malloc_ok_cf : forall U s cid,
Wf_cf U s -> 0 <= cid <= 10 -> atok true (stack_malloc cid s) (stack_malloc_post_cf U s cid).
Proof.
intros U s cid W Hc. pose proof (fs_frames_pos cid Hc) as HN.
unfold stack_malloc. apply atok_bind. apply atok_get. cbn [fst snd].
destruct (fs_probe _ _ _ _) as [[pos hint']|] eqn:EP.
- apply fs_probe_some in EP as (h & H1 & -> & -> & H4); [|exact HN].
apply atok_bind. apply atok_put. cbn [fst snd]. apply atok_ret. cbn -[Z.add Z.modulo fs_frames zupd Wf_cf In].
pose proof (wfs_hints _ (wfc_fakestack _ _ _ _ _ W)) as [L F].
assert (Hh : 0 <= znth 0 cid (fs_hint (st_fs s))).
{ unfold znth. destruct (nth_in_or_default (Z.to_nat cid) (fs_hint (st_fs s)) 0) as [Hin| ->]; [|lia].
exact (proj1 (Forall_forall _ _) F _ Hin). }
pose proof (Z.mod_pos_bound h (fs_frames cid) HN) as MB.
splits; try reflexivity; try lia.
+ apply Wf_cf_push_frame; [exact W | exact Hc | exact MB | lia | unfold frames; apply mem_pos_false; exact H4].
+ eexists. reflexivity.
+ unfold frames. apply mem_pos_false. exact H4.
- apply atok_ret. cbn -[Wf_cf]. split; [exact W | split; [exists (st_fs s); destruct s; reflexivity | reflexivity]].
Qed.

Theorem stack_free_ok_cf : forall U s cid pos,
Wf_cf U s -> In (cid, pos) (frames s) -> stack_free_post_cf U s cid pos.
Proof.
intros U s cid pos W Hin. unfold stack_free_post_cf, stack_free_state.
pose proof (wfc_fakestack _ _ _ _ _ W) as X. destruct X as [[L F] ND LV].
destruct (del_pos_spec _ _ _ ND Hin) as (l1 & l2 & E & ED). unfold frames in *. split.
- unfold Wf_cf in *. apply WfP_cf_set_fs; [exact W|]. constructor; cbn [st_fs set_fs fs_hint fs_live].
+ split; assumption.
+ rewrite ED. rewrite E in ND. exact (NoDup_remove_1 _ _ _ ND).
+ rewrite ED. rewrite E in LV. apply Forall_app in LV as [LV1 LV2]. inversion LV2; subst. apply Forall_app. auto.
- exists l1, l2. cbn. rewrite ED. auto.
Qed.
End STACKCF.
