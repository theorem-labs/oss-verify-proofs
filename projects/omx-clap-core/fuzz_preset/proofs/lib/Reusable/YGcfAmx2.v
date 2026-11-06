(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the walk-side facts for
   c-omx-alloc's generic kit:
   - universe_ok_of_ARcf: ARcf's universe field, by name;
   - img_shadow_vis_cf: the image's shadow is present in the view. Like the donor (img_shadow_vis,
     proofs/libreac/fuzz_grant/lib/A/Prog/GrantRo.v at a970a282587) it is a DEFINITION, a fact of the runtime's
     symbols that the unit supplies, NOT a theorem. The image bounds are the unit's own, the CfImg fields
     cf_img_lo / cf_img_top (generated from the pinned image), never the donor's literals and never one unit's YImgTop.v;
   - amx_realloc_cf_room: realloc's model law over ReallocP.v's realloc_tree_with malloc_cf free_cf, from
     amx's malloc / free laws. The inner free of the old block runs after the malloc, so it needs
     batch_room_cf at the post-malloc state: that is the premise HK, stated on every malloc path from a Wf_cf
     state with the starting state's regions, secondaries and pointer array (the only fields the leading
     free(NULL) keeps fixed that the room reads);
   - amx_realloc_cf_k: the same law with the headroom premise ROOM_cf_k s (RK_realloc + k) (YGcfRoomKeep.v), for
     every malloc headroom step MK; amx_realloc_cf is it with MK := YGcfRoomStep.v's malloc_room_keep_cf.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG06bcf YG07cf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG03cf YG03dcf YGcfAmx ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomStep.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. ARcf's universe field.                                                     *)
Lemma universe_ok_of_ARcf : forall segs B ly S Hp W mem md,
ARcf segs B ly S Hp W mem md -> universe_ok (as_universe B).
Proof. intros segs B ly S Hp W mem md H. exact (amc_universe _ _ _ _ _ (proj1 H)). Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The image's shadow is visible: a fact of the runtime's symbols (the donor's  *)
(*    img_shadow_vis), which the unit supplies. Not proved here.                   *)
Definition img_shadow_vis_cf (segs : list Segment) (B : asyms) : Prop :=
forall ly S Hp (W : world segs) mem md a, ARcf segs B ly S Hp W mem md -> cf_img_lo <= a < cf_img_top ->
aview segs (w_H W) mem (shadow_addr a) <> None.

(* ---------------------------------------------------------------------------- *)
(* 3. realloc.                                                                    *)
(* Equals c-omx-alloc's YGcallRx.realloc_post_x. *)
Definition realloc_post_cf (s : astate) (p : sptr) (n_old n : Z) (r : sptr * astate) : Prop :=
st_nev s <= st_nev (snd r) /\ (length (st_secs s) <= length (st_secs (snd r)))%nat /\ frames (snd r) = frames s /\
(fst r = PNull -> blocks (snd r) = blocks s) /\
(fst r <> PNull -> exists l1 l2, blocks s = l1 ++ (p, n_old) :: l2 /\ blocks (snd r) = l1 ++ l2 ++ [(fst r, n)]).

(* An atok_cf proof at ns = true serves any ns when the post ignores ns: ns only gates a top-level spin. *)
Lemma atok_cf_any_ns : forall A (t : itree astate A) b (Q : bool -> A -> Prop),
(forall b1 b2 a, Q b1 a -> Q b2 a) -> atok_cf true t Q -> atok_cf b t Q.
Proof.
intros A t b Q HQ H. destruct t as [a | q sn k | pc | f]; cbn [atok_cf] in *.
- exact (HQ true b a H).
- exact H.
- discriminate H.
- destruct H.
Qed.

(* Every result an atok_cf proof reaches is reached by a path. *)
Lemma atok_cf_with_path : forall A (t : itree astate A) ns (Q : bool -> A -> Prop),
atok_cf ns t Q -> atok_cf ns t (fun b a => Q b a /\ exists trc, apath t trc a).
Proof.
intros A t. induction t as [a | q sn k IH | pc | f]; cbn [atok_cf]; intros ns Q H.
- split; [exact H|]. exists []. reflexivity.
- destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz.
eapply atok_cf_mono; [|exact (IH z (progz q z) Q (Hk z Hz))].
intros b a0 [HQ [trc Ht]]. split; [exact HQ|]. exists ((q, z) :: trc). cbn [apath]. split; [reflexivity|]. split; [exact Hz | exact Ht].
- exact H.
- destruct H.
Qed.

Lemma no_null_block : forall U pp cc bb s m, WfP_cf U pp cc bb s -> ~ In (PNull, m) (blocks s).
Proof.
intros U pp cc bb s m W Hin. apply In_blocks in Hin as (k & Hk & _ & Hu & _).
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [_ CK].
unfold ck_user in Hu. destruct (ck_beg k); cbn [padd] in Hu; try discriminate; exact CK.
Qed.

Lemma blocks_bytes_blocks : forall s, blocks_bytes s = fold_right (fun b acc => snd b + acc) 0 (blocks s).
Proof.
intros s. unfold blocks_bytes, blocks. induction (st_chunks s) as [|k t IH]; [reflexivity|].
cbn [fold_right filter]. destruct (is_alloc k); cbn [map fold_right snd]; rewrite IH; reflexivity.
Qed.

Lemma snoc_split {X : Type} : forall (A : list X) x m1 y m2, A ++ [x] = m1 ++ y :: m2 -> y <> x ->
exists l2, m2 = l2 ++ [x] /\ A = m1 ++ y :: l2.
Proof.
intros A x m1 y m2 E Hne. induction m2 as [|z m2' _] using rev_ind.
- apply app_inj_tail in E as [_ E]. congruence.
- replace (m1 ++ y :: m2' ++ [z]) with ((m1 ++ y :: m2') ++ [z]) in E by (rewrite <- app_assoc; reflexivity).
apply app_inj_tail in E as [E1 E2]. subst z. exists m2'. split; [reflexivity | exact E1].
Qed.

(* free(NULL) keeps the fields the room reads. *)
Definition nfr (s s1 : astate) : Prop :=
st_regions s1 = st_regions s /\ st_secs s1 = st_secs s /\ st_sec_arr s1 = st_sec_arr s.

Lemma ipost_free_null : forall tr s, ipost (free_cf PNull tr s) (fun r => nfr s (snd r)).
Proof.
intros tr s. unfold free_cf. unfold tick, bind, get, modify, ret.
cbn [ibind ipost fst snd st_internal_inited set_nev].
destruct (st_internal_inited s); cbn [ibind ipost fst snd st_regions st_secs st_sec_arr set_internal_inited set_nev];
unfold nfr; cbn [st_regions st_secs st_sec_arr set_internal_inited set_nev]; repeat split; try reflexivity.
Qed.

(* free(NULL) keeps the depot, so it keeps the call's trace premise (admits_keep). *)
Lemma ipost_free_null_depot : forall tr s, ipost (free_cf PNull tr s) (fun r => st_depot (snd r) = st_depot s).
Proof.
intros tr s. unfold free_cf. unfold tick, bind, get, modify, ret.
cbn [ibind ipost fst snd st_internal_inited set_nev].
destruct (st_internal_inited s); cbn [ibind ipost fst snd st_depot set_internal_inited set_nev]; reflexivity.
Qed.

Lemma ROOM_cf_nfr : forall s s1, nfr s s1 -> ROOM_cf s -> ROOM_cf s1.
Proof.
intros s s1 (R & Sc & Sa) (H1 & H2 & H3). unfold ROOM_cf. split; [rewrite Sa; exact H1|]. split.
- unfold ERRB_ROOM, errb_size_cf in *. rewrite Sc. exact H2.
- unfold batch_room_cf, reg in *. rewrite R. exact H3.
Qed.

(* The realloc tree, for every inner-free room HK supplies. *)
Theorem realloc_cf_atok : forall U s p n_old n tr,
universe_ok U -> Wf_cf U s -> ROOM_cf s -> In (p, n_old) (blocks s) -> 1 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
(forall s1 trc r, Wf_cf U s1 -> nfr s s1 -> apath (malloc_cf n tr s1) trc r -> batch_room_cf (snd r)) ->
atok_cf true (realloc_tree_with malloc_cf free_cf p n tr s) (fun _ r => realloc_post_cf s p n_old n r).
Proof.
intros U s p n_old n tr HU W HR Hp Hn Hlive Htr HK.
pose proof (wfc_slack _ _ _ _ _ W) as SL.
assert (Hpn : p <> PNull) by (intros ->; exact (no_null_block _ _ _ _ s n_old W Hp)).
unfold realloc_tree_with. apply atok_cf_bind.
(* free(NULL) *)
assert (A1 : atok_cf true (free_cf PNull tr s) (free_post_ycf U s PNull 0)).
{ unfold ROOM_cf in HR. destruct HR as (_ & _ & HB). eapply ml_free_cf; eauto. }
eapply atok_cf_mono; [|exact (atok_cf_ipost _ _ _ _ (atok_cf_ipost _ _ _ _ A1 (ipost_free_null tr s)) (ipost_free_null_depot tr s))].
intros b [[] s1] [[F1 N1] D1]. cbn [fst snd] in *.
pose proof (admits_keep U tr s s1 Htr (or_introl D1)) as Htr1.
unfold free_post_ycf in F1. cbn [snd] in F1. destruct F1 as (W1 & Nev1 & X1 & Fr1 & (l1 & l2 & Bs1 & Bl1) & _).
assert (B1 : blocks s1 = blocks s).
{ rewrite Bl1. destruct Bs1 as [[_ E]|E]; [exact E|].
exfalso. apply (no_null_block _ _ _ _ s 0 W). rewrite E. apply in_or_app. right. left. reflexivity. }
pose proof (ROOM_cf_nfr s s1 N1 HR) as HR1. unfold ROOM_cf in HR1. destruct HR1 as (HS1 & HE1 & HB1).
assert (Hlive1 : blocks_bytes s1 + n <= LIVE_MAX) by (rewrite blocks_bytes_blocks, B1, <- blocks_bytes_blocks; exact Hlive).
(* malloc *)
pose proof (atok_cf_ipost _ _ _ _ (malloc_ok_cf U s1 n tr HU W1 ltac:(lia) Hlive1 Htr1 HS1 HE1 HB1) (dep_malloc_cf n tr s1)) as A2.
pose proof (atok_cf_with_path _ _ _ _ A2) as A2p.
assert (A2b : atok_cf b (malloc_cf n tr s1) (fun b0 a => (malloc_post_cf U s1 n b0 a /\
(st_depot (snd a) = st_depot s1 \/ st_depot (snd a) = st_depot s1 ++ [tr])) /\ exists trc, apath (malloc_cf n tr s1) trc a)).
{ apply atok_cf_any_ns; [intros b1 b2 a H; exact H | exact A2p]. }
apply atok_cf_bind. eapply atok_cf_mono; [|exact A2b].
intros b2 [q s2] [[M2 D2] [trc Hpath]]. cbn [fst snd] in D2.
pose proof (admits_keep U tr s1 s2 Htr1 D2) as Htr2.
unfold malloc_post_cf in M2. cbv beta iota in M2. destruct M2 as (W2 & Nev2 & X2 & Fr2 & Bl2 & _).
assert (HB2 : batch_room_cf s2) by exact (HK s1 trc (q, s2) W1 N1 Hpath).
pose proof (proj1 (secs_ext_cf_of_secs_ext _ _ X1)) as L1. pose proof (proj1 X2) as L2.
(* the success arm, for any non-NULL result *)
assert (SUCC : forall q', q' <> PNull -> blocks s2 = blocks s1 ++ [(q', n)] -> ~ In q' (map fst (blocks s1)) ->
atok_cf b2 ((YG00.bind (free_cf p tr) (fun _ => YG00.ret q')) s2) (fun _ r => realloc_post_cf s p n_old n r)).
{ intros q' Hq' Bq Hfresh. apply atok_cf_bind.
assert (Hp2 : In (p, n_old) (blocks s2)) by (rewrite Bq, B1; apply in_or_app; left; exact Hp).
assert (A3 : atok_cf true (free_cf p tr s2) (free_post_ycf U s2 p n_old)) by (eapply ml_free_cf; eauto).
assert (A3b : atok_cf b2 (free_cf p tr s2) (free_post_ycf U s2 p n_old)) by (apply atok_cf_any_ns; [intros b1 b3 a H; exact H | exact A3]).
eapply atok_cf_mono; [|exact A3b]. intros b3 [[] s3] F3. cbn [fst snd]. apply atok_cf_ret.
unfold free_post_ycf in F3. cbn [snd] in F3. destruct F3 as (_ & Nev3 & X3 & Fr3 & (m1 & m2 & Bs3 & Bl3) & _).
pose proof (proj1 (secs_ext_cf_of_secs_ext _ _ X3)) as L3.
cbv beta. unfold realloc_post_cf. cbn [fst snd].
split; [lia|]. split; [lia|]. split; [congruence|]. split; [intros E; contradiction|].
intros _. destruct Bs3 as [[E _]|E]; [contradiction|].
rewrite Bq, B1 in E.
assert (Hne : (p, n_old) <> (q', n)).
{ intros Ep. injection Ep as Ep _. apply Hfresh. rewrite B1, <- Ep. apply in_map_iff. exists (p, n_old). split; [reflexivity | exact Hp]. }
destruct (snoc_split (blocks s) (q', n) m1 (p, n_old) m2 E Hne) as (l2' & Em2 & Es).
exists m1, l2'. split; [exact Es|]. rewrite Bl3, Em2. reflexivity. }
destruct q as [|qo|qr qo|qc qp].
- apply atok_cf_ret. cbv beta iota in Bl2. cbv beta. unfold realloc_post_cf. cbn [fst snd].
split; [lia|]. split; [lia|]. split; [congruence|]. split; [intros _; congruence | intros E; exfalso; apply E; reflexivity].
- apply SUCC; [discriminate | exact (proj1 Bl2) | exact (proj2 Bl2)].
- apply SUCC; [discriminate | exact (proj1 Bl2) | exact (proj2 Bl2)].
- apply SUCC; [discriminate | exact (proj1 Bl2) | exact (proj2 Bl2)].
Qed.

(* The kit's form: safety, progress, no top-level spin, and the post on every path. *)
Theorem amx_realloc_cf_room : forall B s p n_old n tr,
universe_ok (as_universe B) -> Wf_cf (as_universe B) s -> ROOM_cf s -> In (p, n_old) (blocks s) ->
1 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits (as_universe B) tr s ->
(forall s1 trc r, Wf_cf (as_universe B) s1 -> nfr s s1 -> apath (malloc_cf n tr s1) trc r -> batch_room_cf (snd r)) ->
asafe (realloc_tree_with malloc_cf free_cf p n tr s) /\ agprog (realloc_tree_with malloc_cf free_cf p n tr s) /\
is_spin (realloc_tree_with malloc_cf free_cf p n tr s) = false /\
(forall tr' r, apath (realloc_tree_with malloc_cf free_cf p n tr s) tr' r -> realloc_post_cf s p n_old n r).
Proof.
intros B s p n_old n tr HU W HR Hp Hn Hlive Htr HK.
pose proof (realloc_cf_atok (as_universe B) s p n_old n tr HU W HR Hp Hn Hlive Htr HK) as A.
split; [exact (atok_cf_asafe _ _ _ A)|]. split; [exact (atok_cf_agprog _ _ _ A)|].
split; [exact (atok_cf_nospin _ _ A)|].
intros tr' r Hpath. destruct (atok_cf_apath _ _ _ tr' r A Hpath) as [ns H]. exact H.
Qed.

(* free(NULL) keeps the headroom: ROOM_cf_k reads st_sec_arr, errb_size_cf (st_secs) and reg kBatchClass
   (st_regions), the three fields nfr fixes. *)
Lemma ROOM_cf_k_nfr : forall s s1 k, nfr s s1 -> ROOM_cf_k s k -> ROOM_cf_k s1 k.
Proof.
intros s s1 k (R & Sc & Sa) (H1 & H2 & H3). unfold ROOM_cf_k, ERRB_ROOM_k in *.
split; [rewrite Sa; exact H1|]. split.
- unfold errb_size_cf in *. rewrite Sc. exact H2.
- unfold reg in *. rewrite R. exact H3.
Qed.

(* The headroom form, for every malloc headroom step MK. With MK := malloc_room_keep_cf (YGcfRoomStep.v) this
   is amx_realloc_cf below. qtight is part of the kit's premise list; the law does not use it. *)
Theorem amx_realloc_cf_k : forall B s p n_old n tr k,
universe_ok (as_universe B) -> Wf_cf (as_universe B) s -> qtight s -> ROOM_cf_k s (RK_realloc + k) -> In (p, n_old) (blocks s) ->
1 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits (as_universe B) tr s ->
(forall s1 trc r, Wf_cf (as_universe B) s1 -> ROOM_cf_k s1 (S (S k)) -> apath (malloc_cf n tr s1) trc r -> ROOM_cf_k (snd r) (S k)) ->
asafe (realloc_tree_with malloc_cf free_cf p n tr s) /\ agprog (realloc_tree_with malloc_cf free_cf p n tr s) /\
is_spin (realloc_tree_with malloc_cf free_cf p n tr s) = false /\
(forall tr' r, apath (realloc_tree_with malloc_cf free_cf p n tr s) tr' r -> realloc_post_cf s p n_old n r).
Proof.
intros B s p n_old n tr k HU W HQ HRk Hp Hn Hlive Htr MK.
assert (HR : ROOM_cf s) by (apply RK_zero; apply (RK_mono s (RK_realloc + k) 0); [lia | exact HRk]).
apply (amx_realloc_cf_room B s p n_old n tr HU W HR Hp Hn Hlive Htr).
intros s1 trc r W1 N1 Hpath.
assert (R1 : ROOM_cf_k s1 (S (S k))) by exact (ROOM_cf_k_nfr s s1 _ N1 HRk).
pose proof (MK s1 trc r W1 R1 Hpath) as R2.
apply (RK_mono _ _ 0) in R2; [|lia]. apply RK_zero in R2. exact (proj2 (proj2 R2)).
Qed.

(* The kit's realloc law: amx_realloc_cf_k with its headroom step filled by YGcfRoomStep.v's
   malloc_room_keep_cf (all paths, no gflag), whose room_shape_cf comes from the Wf_cf at the post-free(NULL)
   state. *)
Theorem amx_realloc_cf : forall B s p n_old n tr k,
universe_ok (as_universe B) -> Wf_cf (as_universe B) s -> qtight s -> ROOM_cf_k s (RK_realloc + k) -> In (p, n_old) (blocks s) ->
1 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits (as_universe B) tr s ->
asafe (realloc_tree_with malloc_cf free_cf p n tr s) /\ agprog (realloc_tree_with malloc_cf free_cf p n tr s) /\
is_spin (realloc_tree_with malloc_cf free_cf p n tr s) = false /\
(forall tr' r, apath (realloc_tree_with malloc_cf free_cf p n tr s) tr' r -> realloc_post_cf s p n_old n r).
Proof.
intros B s p n_old n tr k HU W HQ HRk Hp Hn Hlive Htr.
apply (amx_realloc_cf_k B s p n_old n tr k HU W HQ HRk Hp Hn Hlive Htr).
intros s1 trc [q s'] W1 R1 Hpath. cbn [snd].
exact (YGcfRoomStep.malloc_room_keep_cf (S k) n tr s1 trc q s' (YGcfRoomStep.room_shape_cf_of_WfP_cf _ _ _ _ _ W1) R1 Hpath).
Qed.
End W.
