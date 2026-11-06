(* CARRIED from commit ae2fa80b0325f09472155bcfce1c36e649d6ff60,
   proofs/cgif/cgif_file_fuzzer/lib/YG06bcf.v, sha256 3c870bfcbc0ed4e82e5be1579afb8ededa57c880034eee0b1db8dcbf50f11c10 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: WfP_cf_pop_add_prim proves WfP_cf's new field wfc_qsize (the queues do not change). *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the CACHE PATH of malloc_cf:
   the errbuf report of the class-full arm, populate_cf, get_from_allocator_cf, cache_alloc_cf, and the
   step that pops the cached record into a new allocated chunk. cgif's YG06.v (populate_okx :326,
   get_from_allocator_okx :441, pop_ok :611, cache_alloc_okx :645), YG06.v:239 (cls_ok_add_ko) and
   YG02.v:309 (WfP_add_prim_chunk), restated over WfP_cf (YG01cf.v) and atok_cf (YGcfTok.v), on top of
   YG02cf.v / YG06cf.v.
   What differs from cgif:
   - no event regime: cgif's preg / regime premises (YG06.v:443-444, :646) and the BigP / nrecZ
     bookkeeping (cache_alloc_postx :553-556, BigP_carve :591, proom_big :581) are gone. Compl0 is a field
     of WfP_cf, so a state that has popped a record and not yet stored it in a chunk is NOT a WfP_cf state;
     cache_alloc_post_cf therefore names the state BEFORE the pop, and WfP_cf_pop_add_prim moves the popped
     record into the new chunk in one step.
   - the class-full arm: map_more_user_cf may run errb_report_cf (YG00cf.v:154-157), which ticks and
     appends errbuf control entries to st_secs. errb_report_cf_ok proves it, under the call premise
     ERRB_ROOM (YG00cf.v:114). Its states are related to the start by errb_frame (only st_secs and st_nev
     move) and secs_ext_cf (every non-control entry keeps its length and size). The arm costs one unit of
     the cc slack (the errbuf size entry is appended once without a tick); it never also appends a chunk.
   - class kBatchClass keeps cgif's text, whose map mcheck (YG00.v:285) needs batch_room_cf (YG00cf.v).
   cgif's YG06.v / YG02.v are NOT edited. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YG02cf YGcfTok YG06cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The frame relations of the cf instance.                                    *)
(* cgif's secs_ext (YG01.v:546-548), restricted to the real secondaries: the errbuf control entries of
   YG00cf.v (negative sm_size) are re-tagged and resized in place. The length clause is what the layout's
   index pinning needs (layout_le, YG0f.v:65-70). *)
Definition secs_ext_cf (s s' : astate) : Prop :=
(length (st_secs s) <= length (st_secs s'))%nat /\
forall r sm, nth_error (st_secs s) r = Some sm -> is_errb_any sm = false ->
exists sm', nth_error (st_secs s') r = Some sm' /\ sm_len sm' = sm_len sm /\ sm_size sm' = sm_size sm.

Lemma secs_ext_cf_refl : forall s, secs_ext_cf s s.
Proof. intros s. split; [lia|]. intros r sm E _. exists sm. auto. Qed.

Lemma secs_ext_cf_trans : forall s1 s2 s3, secs_ext_cf s1 s2 -> secs_ext_cf s2 s3 -> secs_ext_cf s1 s3.
Proof.
intros s1 s2 s3 [L12 H12] [L23 H23]. split; [lia|]. intros r sm E N.
destruct (H12 r sm E N) as (sm2 & E2 & A2 & B2).
assert (N2 : is_errb_any sm2 = false) by (unfold is_errb_any in *; rewrite B2; exact N).
destruct (H23 r sm2 E2 N2) as (sm3 & E3 & A3 & B3). exists sm3. split; [exact E3|]. split; congruence.
Qed.

Lemma secs_ext_cf_of_secs_ext : forall s s', secs_ext s s' -> secs_ext_cf s s'.
Proof.
intros s s' H. split.
- destruct (Nat.le_gt_cases (length (st_secs s)) (length (st_secs s'))) as [Hl|Hg]; [exact Hl|].
destruct (nth_error (st_secs s) (length (st_secs s'))) as [sm|] eqn:E.
+ destruct (H _ _ E) as (sm' & E' & _). apply nth_error_lt in E'. lia.
+ apply nth_error_None in E. lia.
- intros r sm E _. exact (H r sm E).
Qed.

(* Only st_secs and st_nev differ: the errbuf steps. *)
Definition errb_frame (s s' : astate) : Prop := s' = set_nev (st_nev s') (set_secs (st_secs s') s).

Lemma errb_frame_refl : forall s, errb_frame s s.
Proof. intros s. unfold errb_frame. destruct s. reflexivity. Qed.

Lemma errb_frame_trans : forall s1 s2 s3, errb_frame s1 s2 -> errb_frame s2 s3 -> errb_frame s1 s3.
Proof. unfold errb_frame. intros s1 s2 s3 E2 E3. rewrite E3 at 1. rewrite E2. reflexivity. Qed.

(* cgif's regs_only (YG06.v:541-544), with st_secs and st_nev relaxed as the errbuf needs. *)
Definition regs_only_cf (s s' : astate) : Prop :=
st_chunks s' = st_chunks s /\ st_sec_arr s' = st_sec_arr s /\ st_sec_reserved s' = st_sec_reserved s /\
st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\
st_internal_inited s' = st_internal_inited s /\ st_nev s <= st_nev s' /\ secs_ext_cf s s'.

Lemma regs_only_cf_refl : forall s, regs_only_cf s s.
Proof. intros s. unfold regs_only_cf. repeat split; try reflexivity; try lia. intros r sm E _. exists sm. auto. Qed.

Lemma regs_only_cf_trans : forall s1 s2 s3, regs_only_cf s1 s2 -> regs_only_cf s2 s3 -> regs_only_cf s1 s3.
Proof.
intros s1 s2 s3 (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1 & I1 & J1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2 & I2 & J2).
unfold regs_only_cf. repeat split; try congruence; try lia.
- exact (proj1 (secs_ext_cf_trans _ _ _ J1 J2)).
- exact (proj2 (secs_ext_cf_trans _ _ _ J1 J2)).
Qed.

Lemma regs_only_cf_of_regs_only : forall s s', regs_only s s' -> regs_only_cf s s'.
Proof.
intros s s' (A & B & C & D & E & F & G & H & I & J). unfold regs_only_cf.
repeat split; try assumption; try lia.
- rewrite B. lia.
- intros r sm Es _. exists sm. rewrite B. auto.
Qed.

Lemma regs_only_cf_frame : forall s s', errb_frame s s' -> st_nev s <= st_nev s' -> secs_ext_cf s s' -> regs_only_cf s s'.
Proof.
intros s s' E N X. unfold regs_only_cf.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj N X))))))))); rewrite E; reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The errbuf control entries.                                                 *)
Definition errb_retire_f (sm : secmap) : secmap :=
if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm.

Lemma find_sz_spec : forall l i j, find_sz l i = Some j ->
(i <= j)%nat /\ exists sm, nth_error l (j - i) = Some sm /\ is_errb_sz sm = true.
Proof.
induction l as [|sm t IH]; intros i j H; cbn [find_sz] in H; [discriminate|].
destruct (is_errb_sz sm) eqn:E.
- injection H as <-. split; [lia|]. exists sm. rewrite Nat.sub_diag. cbn. auto.
- destruct (IH (S i) j H) as [Hle (sm' & E' & S')]. split; [lia|]. exists sm'.
replace (j - i)%nat with (S (j - S i)) by lia. cbn. auto.
Qed.

Lemma find_sz_app_ctl : forall l x i, is_errb_sz x = false -> find_sz (l ++ [x]) i = find_sz l i.
Proof.
induction l as [|sm t IH]; intros x i Hx; cbn [find_sz app].
- rewrite Hx. reflexivity.
- destruct (is_errb_sz sm); [reflexivity | apply IH, Hx].
Qed.

Lemma find_sz_app_none : forall l x i, find_sz l i = None -> is_errb_sz x = true -> find_sz (l ++ [x]) i = Some (i + length l)%nat.
Proof.
induction l as [|sm t IH]; intros x i H Hx; cbn [find_sz app length] in *.
- rewrite Hx. f_equal. lia.
- destruct (is_errb_sz sm); [discriminate|]. rewrite (IH x (S i) H Hx). f_equal. lia.
Qed.

Lemma find_sz_retire : forall l i, find_sz (map errb_retire_f l) i = find_sz l i.
Proof.
induction l as [|sm t IH]; intros i; [reflexivity|]. cbn [map find_sz]. rewrite IH.
unfold errb_retire_f. destruct (is_errb_cap sm) eqn:Ec; [|reflexivity].
replace (is_errb_sz (mkSec (sm_len sm) ERRB_DEAD_TAG false)) with false by reflexivity.
replace (is_errb_sz sm) with false; [reflexivity|].
unfold is_errb_cap, is_errb_sz in *. apply Z.eqb_eq in Ec. rewrite Ec. reflexivity.
Qed.

Lemma find_sz_lupd : forall l j k v, find_sz l j = Some k -> is_errb_sz v = true -> find_sz (lupd l (k - j) v) j = Some k.
Proof.
induction l as [|sm t IH]; intros j k v H Hv; cbn [find_sz] in H; [discriminate|].
destruct (is_errb_sz sm) eqn:E.
- injection H as <-. rewrite Nat.sub_diag. cbn [lupd find_sz]. rewrite Hv. reflexivity.
- pose proof (find_sz_spec t (S j) k H) as [Hle _]. replace (k - j)%nat with (S (k - S j)) by lia.
cbn [lupd find_sz]. rewrite E. apply IH; assumption.
Qed.

Lemma Forall_lupd {X} : forall (P : X -> Prop) l i v, Forall P l -> P v -> Forall P (lupd l i v).
Proof.
intros P l. induction l as [|h t IH]; intros [|i] v H Hv; cbn [lupd]; try exact H.
- inversion H; subst. constructor; assumption.
- inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma needed_size_nonneg : forall n, 0 <= n -> 0 <= needed_size n.
Proof.
intros n Hn. unfold needed_size. pose proof (needed_primary_bounds n Hn) as (_ & [N _] & _).
pose proof (rz_size_bounds n) as [[R _] _]. destruct (from_primary n); lia.
Qed.

Lemma ctl_not_cap : forall sm, is_errb_any sm = false -> is_errb_cap sm = false.
Proof.
intros sm H. unfold is_errb_any, is_errb_cap, ERRB_CAP_TAG in *. apply Z.ltb_ge in H.
apply Z.eqb_neq. lia.
Qed.

Section ERRB.
Context {cp : CfParams}.

(* A secondary chunk's entry is a real secondary, never a control entry. *)
Lemma chunk_entry_real : forall s k r o, chunk_ok_cf s k -> ck_beg k = PSec r o ->
exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\ is_errb_any sm = false.
Proof.
intros s k r o [Hn CK] E. rewrite E in CK. destruct CK as (_ & _ & sm & Es & Hl & Hs & _).
exists sm. split; [exact Es|]. split; [exact Hl|].
unfold is_errb_any. rewrite Hs. apply Z.ltb_ge. apply needed_size_nonneg. lia.
Qed.

(* Any rewrite of st_secs that keeps every real secondary in place, adds no live entry, keeps the length
   bound and is paid for by st_nev keeps WfP_cf. *)
Lemma WfP_cf_secs_ctl : forall U pp cc bb s l',
WfP_cf U pp cc bb s ->
(length (st_secs s) <= length l')%nat ->
(forall r sm, nth_error (st_secs s) r = Some sm -> is_errb_any sm = false -> nth_error l' r = Some sm) ->
(forall r sm', nth_error l' r = Some sm' -> sm_live sm' = true -> nth_error (st_secs s) r = Some sm') ->
Forall (fun sm => 0 <= sm_len sm <= cf_nob) l' ->
Z.of_nat (length l') + cc <= st_nev s ->
WfP_cf U pp cc bb (set_secs l' s) /\ secs_ext_cf s (set_secs l' s).
Proof.
intros U pp cc bb s l' W HL HK HLive HLen Hev.
split; [|split; [exact HL | intros r sm E N; exists sm; split; [apply HK; assumption | split; reflexivity]]].
pose proof (wfc_chunks _ _ _ _ _ W) as CK. pose proof (wfc_secondary _ _ _ _ _ W) as X.
destruct W. constructor; try assumption.
all: lazymatch goal with
| |- Forall (chunk_ok_cf _) _ =>
apply Forall_forall; intros k Hk; pose proof (proj1 (Forall_forall _ _) CK k Hk) as CKk;
destruct CKk as [Hn CKb]; split; [exact Hn|]; cbn [st_secs set_secs];
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try exact CKb;
destruct (chunk_entry_real s k r o (proj1 (Forall_forall _ _) CK k Hk) Eb) as (sm & Es & _ & Hc);
destruct CKb as (A & B & sm0 & Es0 & C); rewrite Es in Es0; injection Es0 as <-;
split; [exact A|]; split; [exact B|]; exists sm; split; [apply HK; assumption | exact C]
| |- wf_quar _ => apply (wf_quar_ext s); [reflexivity | reflexivity | reflexivity | assumption]
| |- wf_fs _ => apply (wf_fs_ext s); [reflexivity | assumption]
| |- wf_sec_cf _ =>
constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_secs];
[ exact (wsc_nodup _ X) | exact (wsc_arr_chunks _ X) | | exact (wsc_reserved _ X) | exact (wsc_reserved_al _ X) | exact HLen ];
intros r; split;
[ intros Hin; pose proof (proj1 (wsc_arr_chunks _ X r) Hin) as (k & Hk & Hb);
destruct (chunk_entry_real s k r kPage (proj1 (Forall_forall _ _) CK k Hk) Hb) as (sm & Es & Hl & Hn);
exists sm; split; [apply HK; assumption | exact Hl]
| intros (sm' & E' & Hl'); apply (proj2 (wsc_arr_live _ X r)); exists sm'; split; [apply HLive; assumption | exact Hl'] ]
| |- Z.of_nat (length (st_secs _)) + _ <= _ => exact Hev
end.
Qed.

Lemma errb_size_nonneg_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> 0 <= errb_size_cf s.
Proof.
intros U pp cc bb s W. pose proof (wsc_lens _ (wfc_secondary _ _ _ _ _ W)) as L. unfold errb_size_cf.
destruct (find_sz (st_secs s) 0) as [i|]; [|lia]. destruct (nth_error (st_secs s) i) as [sm|] eqn:E; [|lia].
apply nth_error_In in E. exact (proj1 (proj1 (Forall_forall _ _) L _ E)).
Qed.

Section MAP.
Context {ci : CfImg}.

(* errb_map_cf (YG00cf.v:129-134): tick, ask for the map (a refusal is MmapOrDie, a spin), retire the old
   capacity entry, append the new one. *)
Lemma errb_map_cf_ok : forall U pp cc bb s want ns,
WfP_cf U pp cc bb s -> 0 < want -> round_up want kPage <= cf_nob ->
atok_cf ns (errb_map_cf want s) (fun _ r => let s' := snd r in
WfP_cf U pp cc bb s' /\ errb_frame s s' /\ st_nev s' = st_nev s + 1 /\
length (st_secs s') = S (length (st_secs s)) /\ secs_ext_cf s s' /\ find_sz (st_secs s') 0 = find_sz (st_secs s) 0).
Proof.
intros U pp cc bb s want ns W Hw Hle.
pose proof (round_up_ge want kPage ltac:(unfold kPage; lia)) as [[R1 _] _].
unfold errb_map_cf. cbv beta zeta. apply atok_cf_bind. apply atok_cf_tick. cbn [fst snd].
pose proof (WfP_cf_tick U pp cc bb s W) as W1. set (s1 := set_nev (st_nev s + 1) s) in *.
apply atok_cf_bind. apply atok_cf_askz; [apply areq_ok_cf_errb; assumption|].
intros z Hz. cbn in Hz. cbn [fst snd]. destruct Hz as [-> | ->].
- cbn [progz Z.eqb]. apply atok_cf_spin.
- cbn [progz Z.eqb Pos.eqb]. apply atok_cf_bind. unfold errb_retire. apply atok_cf_modify. cbn [fst snd].
apply atok_cf_modify. cbv beta. cbn [snd st_secs set_secs].
change (map (fun sm => if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm) (st_secs s1))
with (map errb_retire_f (st_secs s1)).
set (cap := mkSec (round_up want kPage) ERRB_CAP_TAG false).
set (l' := map errb_retire_f (st_secs s1) ++ [cap]).
change (set_secs l' (set_secs (map errb_retire_f (st_secs s1)) s1)) with (set_secs l' s1).
pose proof (wsc_lens _ (wfc_secondary _ _ _ _ _ W)) as Slen.
pose proof (wfc_secs_ev _ _ _ _ _ W) as Sev.
assert (HL : length l' = S (length (st_secs s))) by (subst l'; rewrite length_app, length_map; cbn; lia).
destruct (WfP_cf_secs_ctl U pp cc bb s1 l' W1) as [W2 X2].
+ rewrite HL. cbn. lia.
+ intros r sm E N. subst l'. rewrite nth_error_app1 by (rewrite length_map; eapply nth_error_lt; exact E).
rewrite nth_error_map, E. cbn. unfold errb_retire_f. rewrite (ctl_not_cap sm N). reflexivity.
+ intros r sm' E Hl. subst l'. destruct (Nat.lt_ge_cases r (length (map errb_retire_f (st_secs s1)))) as [Hr|Hr].
* rewrite nth_error_app1 in E by exact Hr. rewrite nth_error_map in E.
destruct (nth_error (st_secs s1) r) as [sm|] eqn:Es; cbn in E; [|discriminate]. injection E as <-.
unfold errb_retire_f in Hl |- *. destruct (is_errb_cap sm); [discriminate Hl | reflexivity].
* rewrite nth_error_app2 in E by exact Hr. destruct (r - length (map errb_retire_f (st_secs s1)))%nat as [|m];
cbn in E; [injection E as <-; discriminate Hl | destruct m; discriminate].
+ subst l'. apply Forall_app. split.
* apply Forall_map. eapply Forall_impl; [|exact Slen]. intros sm H. unfold errb_retire_f. destruct (is_errb_cap sm); exact H.
* constructor; [|constructor]. subst cap. cbn [sm_len]. lia.
+ rewrite HL. subst s1. cbn [st_nev set_nev]. lia.
+ split; [exact W2|]. split; [unfold errb_frame; reflexivity|]. split; [reflexivity|]. split; [exact HL|].
split; [exact X2|]. cbn [st_secs set_secs]. subst l'. rewrite find_sz_app_ctl by reflexivity. apply find_sz_retire.
Qed.

(* errb_set_size (YG00cf.v:98-103): update the size entry in place, or append it. *)
Lemma errb_set_size_ok : forall U pp cc bb s v ns,
WfP_cf U pp cc bb s -> 0 <= v <= cf_nob ->
(find_sz (st_secs s) 0 = None -> Z.of_nat (length (st_secs s)) + 1 + cc <= st_nev s) ->
atok_cf ns (errb_set_size v s) (fun _ r => let s' := snd r in
WfP_cf U pp cc bb s' /\ errb_frame s s' /\ st_nev s' = st_nev s /\ secs_ext_cf s s' /\
find_sz (st_secs s') 0 <> None /\ errb_size_cf s' = v).
Proof.
intros U pp cc bb s v ns W Hv Hslack.
pose proof (wsc_lens _ (wfc_secondary _ _ _ _ _ W)) as Slen. pose proof (wfc_secs_ev _ _ _ _ _ W) as Sev.
set (new := mkSec v ERRB_SZ_TAG false).
unfold errb_set_size. apply atok_cf_modify. cbv beta. cbn [snd].
destruct (find_sz (st_secs s) 0) as [i|] eqn:Ef.
- pose proof (find_sz_spec _ _ _ Ef) as [_ (smz & Ez & Sz)]. rewrite Nat.sub_0_r in Ez.
assert (Hi : (i < length (st_secs s))%nat) by (eapply nth_error_lt; exact Ez).
fold new.
destruct (WfP_cf_secs_ctl U pp cc bb s (lupd (st_secs s) i new) W) as [W2 X2].
+ rewrite lupd_length. lia.
+ intros r sm E N. destruct (Nat.eq_dec r i) as [->|Hne].
* rewrite Ez in E. injection E as <-. unfold is_errb_any, is_errb_sz, ERRB_SZ_TAG in *.
apply Z.eqb_eq in Sz. rewrite Sz in N. discriminate N.
* rewrite nth_error_lupd_other by (intros ->; apply Hne; reflexivity). exact E.
+ intros r sm' E Hl. destruct (Nat.eq_dec r i) as [->|Hne].
* rewrite nth_error_lupd_same in E by exact Hi. injection E as <-. discriminate Hl.
* rewrite nth_error_lupd_other in E by (intros ->; apply Hne; reflexivity). exact E.
+ apply Forall_lupd; [exact Slen | subst new; cbn; lia].
+ rewrite lupd_length. exact Sev.
+ split; [exact W2|]. split; [unfold errb_frame; destruct s; reflexivity|]. split; [reflexivity|]. split; [exact X2|].
cbn [st_secs set_secs]. pose proof (find_sz_lupd (st_secs s) 0 i new Ef eq_refl) as F. rewrite Nat.sub_0_r in F.
split; [rewrite F; discriminate|]. unfold errb_size_cf. cbn [st_secs set_secs]. rewrite F.
rewrite nth_error_lupd_same by exact Hi. reflexivity.
- fold new. destruct (WfP_cf_secs_ctl U pp cc bb s (st_secs s ++ [new]) W) as [W2 X2].
+ rewrite length_app. cbn. lia.
+ intros r sm E N. rewrite nth_error_app1 by (eapply nth_error_lt; exact E). exact E.
+ intros r sm' E Hl. destruct (Nat.lt_ge_cases r (length (st_secs s))) as [Hr|Hr].
* rewrite nth_error_app1 in E by exact Hr. exact E.
* rewrite nth_error_app2 in E by exact Hr. destruct (r - length (st_secs s))%nat as [|m];
cbn in E; [injection E as <-; discriminate Hl | destruct m; discriminate].
+ apply Forall_app. split; [exact Slen|]. constructor; [|constructor]. subst new. cbn. lia.
+ rewrite length_app. cbn [length]. specialize (Hslack eq_refl). lia.
+ split; [exact W2|]. split; [unfold errb_frame; destruct s; reflexivity|]. split; [reflexivity|]. split; [exact X2|].
cbn [st_secs set_secs]. pose proof (find_sz_app_none (st_secs s) new 0 Ef eq_refl) as F. cbn [Nat.add] in F.
split; [rewrite F; discriminate|]. unfold errb_size_cf. cbn [st_secs set_secs]. rewrite F.
rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
Qed.

(* errb_append_cf (YG00cf.v:140-150): one Printf into the buffer, mapping or remapping it as needed. *)
Lemma errb_append_cf_ok : forall U pp cc bb s len ns,
WfP_cf U pp cc bb s -> 0 < len <= kPage -> errb_size_cf s + len + kPage <= cf_nob ->
(find_sz (st_secs s) 0 = None -> Z.of_nat (length (st_secs s)) + 1 + cc <= st_nev s) ->
atok_cf ns (errb_append_cf len s) (fun _ r => let s' := snd r in
WfP_cf U pp cc bb s' /\ errb_frame s s' /\ st_nev s <= st_nev s' /\ secs_ext_cf s s' /\
find_sz (st_secs s') 0 <> None /\ errb_size_cf s' <= errb_size_cf s + len).
Proof.
intros U pp cc bb s len ns W Hlen Hroom Hslack.
pose proof (errb_size_nonneg_cf U pp cc bb s W) as Z0. pose proof cf_nob_sec_len as NB.
assert (RU : forall w, 0 < w -> round_up w kPage <= w + kPage).
{ intros w Hw0. pose proof (round_up_ge w kPage ltac:(unfold kPage; lia)) as [[_ R2] _]. lia. }
(* the tail shared by both branches: errb_set_size after zero or more maps *)
assert (TAIL : forall s1 ns1 v, WfP_cf U pp cc bb s1 -> errb_frame s s1 -> st_nev s <= st_nev s1 -> secs_ext_cf s s1 ->
find_sz (st_secs s1) 0 = find_sz (st_secs s) 0 ->
Z.of_nat (length (st_secs s1)) - Z.of_nat (length (st_secs s)) <= st_nev s1 - st_nev s ->
0 <= v <= cf_nob -> v <= errb_size_cf s + len ->
atok_cf ns1 (errb_set_size v s1) (fun _ r => let s' := snd r in
WfP_cf U pp cc bb s' /\ errb_frame s s' /\ st_nev s <= st_nev s' /\ secs_ext_cf s s' /\
find_sz (st_secs s') 0 <> None /\ errb_size_cf s' <= errb_size_cf s + len)).
{ intros s1 ns1 v W1 F1 N1 X1 Z1 L1 Hv Hvs.
eapply atok_cf_mono; [|apply (errb_set_size_ok U pp cc bb s1 v ns1 W1 Hv)].
- intros b r (W2 & F2 & N2 & X2 & Z2 & S2). cbv beta in *. split; [exact W2|].
split; [exact (errb_frame_trans _ _ _ F1 F2)|]. split; [lia|]. split; [exact (secs_ext_cf_trans _ _ _ X1 X2)|].
split; [exact Z2 | lia].
- intros E. rewrite Z1 in E. specialize (Hslack E). lia. }
unfold errb_append_cf. apply atok_cf_bind. apply atok_cf_get. cbn [fst snd].
destruct (errb_mapped_cf s) eqn:Em; cbn [negb].
- cbv zeta. apply atok_cf_bind.
apply (atok_cf_if _ (errb_cap_cf s <? errb_size_cf s + len)); intros Hc.
+ eapply atok_cf_mono; [|apply (errb_map_cf_ok U pp cc bb s (errb_size_cf s + len) ns W); [lia | pose proof (RU (errb_size_cf s + len)); lia]].
intros b [[] s1] (W1 & F1 & N1 & L1 & X1 & Z1). cbv beta in *. cbn [fst snd] in *.
apply (TAIL s1 b); first [assumption | lia | (rewrite L1; lia) | (unfold kPage in *; lia)].
+ apply atok_cf_ret. cbn [fst snd].
apply (TAIL s ns); first [assumption | lia | apply errb_frame_refl | apply secs_ext_cf_refl | reflexivity | (unfold kPage in *; lia)].
- apply atok_cf_bind.
eapply atok_cf_mono; [|apply (errb_map_cf_ok U pp cc bb s ERRB_INIT ns W); [unfold ERRB_INIT; lia | unfold ERRB_INIT, kPage, round_up, SEC_LEN_MAX in *; cbn; lia]].
intros b [[] s1] (W1 & F1 & N1 & L1 & X1 & Z1). cbv beta in *. cbn [fst snd] in *.
apply atok_cf_bind. apply atok_cf_get. cbn [fst snd]. apply atok_cf_bind.
apply (atok_cf_if _ (errb_cap_cf s1 <? len)); intros Hc.
+ eapply atok_cf_mono; [|apply (errb_map_cf_ok U pp cc bb s1 len b W1); [lia | pose proof (RU len); unfold kPage, SEC_LEN_MAX in *; lia]].
intros b2 [[] s2] (W2 & F2 & N2 & L2 & X2 & Z2). cbv beta in *. cbn [fst snd] in *.
apply (TAIL s2 b2 len W2 (errb_frame_trans _ _ _ F1 F2));
first [exact (secs_ext_cf_trans _ _ _ X1 X2) | lia | congruence | (rewrite L2, L1; lia) | (unfold kPage, SEC_LEN_MAX in *; lia)].
+ apply atok_cf_ret. cbn [fst snd].
apply (TAIL s1 b len W1 F1); first [assumption | lia | (rewrite L1; lia) | (unfold kPage, SEC_LEN_MAX in *; lia)].
Qed.

Lemma ndigits_bounds : forall z, 1 <= ndigits z <= 5.
Proof. intros z. unfold ndigits. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

(* The class-full report (YG00cf.v:154-157): nothing when the class's byte is set, else two Printfs. *)
Lemma errb_report_cf_ok : forall U pp cc bb s c ns,
WfP_cf U pp cc bb s -> 1 <= cc -> ERRB_ROOM s ->
atok_cf ns (errb_report_cf c s) (fun _ r => let s' := snd r in
WfP_cf U pp (cc - 1) bb s' /\ errb_frame s s' /\ st_nev s <= st_nev s' /\ secs_ext_cf s s').
Proof.
intros U pp cc bb s c ns W Hcc Hroom. unfold ERRB_ROOM in Hroom.
pose proof (wfc_slack _ _ _ _ _ W) as SL. pose proof (wfc_secs_ev _ _ _ _ _ W) as Sev.
assert (W0 : WfP_cf U pp (cc - 1) bb s) by (eapply WfP_cf_weaken; [exact W | lia | lia | lia]).
pose proof (ndigits_bounds c) as D1. pose proof (ndigits_bounds (class_size c)) as D2.
unfold errb_report_cf. apply atok_cf_bind. apply atok_cf_get. cbn [fst snd].
destruct (exh_mem_cf s c).
- apply atok_cf_ret. cbn [snd]. split; [exact W0|]. split; [apply errb_frame_refl|]. split; [lia | apply secs_ext_cf_refl].
- apply atok_cf_bind.
eapply atok_cf_mono; [|apply (errb_append_cf_ok U pp (cc - 1) bb s exh_len1 ns W0); [unfold exh_len1, kPage; lia | unfold exh_len1, kPage in *; lia | intros _; lia]].
intros b [[] s1] (W1 & F1 & N1 & X1 & Z1 & S1). cbv beta in *. cbn [fst snd] in *.
pose proof (errb_size_nonneg_cf U pp (cc - 1) bb s W0).
eapply atok_cf_mono; [|apply (errb_append_cf_ok U pp (cc - 1) bb s1 (exh_len2 c) b W1); [unfold exh_len2, kPage; lia | unfold exh_len1, exh_len2, kPage in *; lia | intros E; contradiction]].
intros b2 [[] s2] (W2 & F2 & N2 & X2 & _ & _). cbv beta in *. cbn [fst snd] in *.
split; [exact W2|]. split; [exact (errb_frame_trans _ _ _ F1 F2)|]. split; [lia | exact (secs_ext_cf_trans _ _ _ X1 X2)].
Qed.
End MAP.
End ERRB.

(* ---------------------------------------------------------------------------- *)
(* 3. Class geometry, cgif's fa_len_bound (YG06.v:261), cls_ok_populate (:207) and *)
(*    cls_ok_add_ko (:239) over cls_ok_cf.                                          *)
Lemma atok_cf_set_region {cp : CfParams} : forall ns c r s (Q : bool -> unit * astate -> Prop),
Q ns (tt, upd_reg c r s) -> atok_cf ns (set_region c r s) Q.
Proof. intros ns c r s Q H. exact H. Qed.
Lemma atok_cf_set_pc {cp : CfParams} : forall ns c p s (Q : bool -> unit * astate -> Prop),
Q ns (tt, upd_pc c p s) -> atok_cf ns (set_pc c p s) Q.
Proof. intros ns c p s Q H. exact H. Qed.

Lemma fa_len_bound_cf : forall c r p i ko bo,
cls_ok_cf c r p i ko bo -> 0 < class_size c -> class_size c * fa_len (rg_free r) <= rg_alloc_user r.
Proof.
intros c r p i ko bo C Hsz.
pose proof (wrc_nodup _ _ _ _ _ _ C) as ND. pose proof (wrc_elems _ _ _ _ _ _ C) as EL. pose proof (wrc_runs _ _ _ _ _ _ C) as R.
apply NoDup_app_iff in ND as (ND & _ & _). apply Forall_app in EL as [EL _].
rewrite <- (fa_elems_length (class_size c)) by exact R.
apply multiples_bound; [exact Hsz | pose proof (wrc_alloc _ _ _ _ _ _ C); lia | exact (wrc_alloc_al _ _ _ _ _ _ C) | exact ND | exact EL].
Qed.

Lemma cls_ok_cf_populate : forall c r p i ko bo,
cls_ok_cf c r p i ko bo -> 0 < class_size c ->
let cnt := (rg_mapped_user r - rg_alloc_user r) / class_size c in
1 <= cnt -> 4 * (fa_len (rg_free r) + cnt) <= rg_mapped_fa r ->
cls_ok_cf c (mkRegion (rg_mapped_user r) (rg_alloc_user r + cnt * class_size c) (rg_mapped_fa r)
(FRun (rg_alloc_user r) cnt :: rg_free r) (rg_holes r)) p i ko bo.
Proof.
intros c r p i ko bo C Hsz cnt Hcnt Hfa.
pose proof (wrc_alloc _ _ _ _ _ _ C) as A. pose proof (wrc_alloc_al _ _ _ _ _ _ C) as Aal.
pose proof (wrc_nodup _ _ _ _ _ _ C) as ND. pose proof (wrc_elems _ _ _ _ _ _ C) as EL.
assert (Hdiv : cnt * class_size c <= rg_mapped_user r - rg_alloc_user r).
{ subst cnt. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
constructor; cbnr; try (exact (wrc_mapped_al _ _ _ _ _ _ C)); try (exact (wrc_fa _ _ _ _ _ _ C)); try (exact (wrc_fa_bound _ _ _ _ _ _ C));
try (exact (wrc_cache _ _ _ _ _ _ C)); try (exact (wrc_mapped_bound _ _ _ _ _ _ C)); try (exact (wrc_holes _ _ _ _ _ _ C)).
- nia.
- pose proof (wrc_carved _ _ _ _ _ _ C). nia.
- rewrite Z.add_mod, Aal, Z_mod_mult by lia. reflexivity.
- cbn [fa_len]. lia.
- constructor; [lia | exact (wrc_runs _ _ _ _ _ _ C)].
- rewrite fa_elems_cons_run, <- app_assoc. apply NoDup_app_iff. split; [apply run_elems_NoDup; lia|]. split; [exact ND|].
intros x Hx Hy. apply In_run_elems in Hx as (j & Hj & ->).
pose proof (proj1 (Forall_forall _ _) EL _ Hy) as [B _]. nia.
- rewrite fa_elems_cons_run, <- app_assoc. apply Forall_app. split.
+ apply Forall_forall. intros x Hx. apply In_run_elems in Hx as (j & Hj & ->). split; [nia|].
rewrite Z.add_mod, Aal, Z_mod_mult by lia. reflexivity.
+ eapply Forall_impl; [|exact EL]. cbn beta. intros x [B M]. split; [nia | exact M].
Qed.

Lemma cls_ok_cf_add_ko : forall c r p i ko bo x,
cls_ok_cf c r p i ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
cls_ok_cf c r p i (ko ++ [x]) bo.
Proof.
intros c r p i ko bo x C Hni Hx Hm.
assert (HP : Permutation (x :: fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
(fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ (ko ++ [x]) ++ bo)).
{ replace (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ (ko ++ [x]) ++ bo)
with ((fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko) ++ x :: bo) by (rewrite <- !app_assoc; reflexivity).
replace (x :: fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
with (x :: (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko) ++ bo) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_middle. }
constructor; try (exact (wrc_alloc _ _ _ _ _ _ C)); try (exact (wrc_carved _ _ _ _ _ _ C)); try (exact (wrc_mapped_al _ _ _ _ _ _ C));
try (exact (wrc_alloc_al _ _ _ _ _ _ C)); try (exact (wrc_fa _ _ _ _ _ _ C)); try (exact (wrc_fa_bound _ _ _ _ _ _ C));
try (exact (wrc_fa_len _ _ _ _ _ _ C)); try (exact (wrc_runs _ _ _ _ _ _ C)); try (exact (wrc_holes _ _ _ _ _ _ C));
try (exact (wrc_cache _ _ _ _ _ _ C)); try (exact (wrc_mapped_bound _ _ _ _ _ _ C)).
- eapply Permutation_NoDup; [exact HP|]. constructor; [exact Hni | exact (wrc_nodup _ _ _ _ _ _ C)].
- eapply Forall_Permutation; [exact HP|]. constructor; [split; [exact Hx | exact Hm] | exact (wrc_elems _ _ _ _ _ _ C)].
Qed.

Lemma last_in_ne {A : Type} : forall (l : list A) d, l <> [] -> In (last l d) l.
Proof.
intros l d Hne. rewrite <- (removelast_app_last l d Hne) at 2. apply in_or_app. right. left. reflexivity.
Qed.

Section CACHE.
Context {cp : CfParams}.

(* populate_cf's carve (YG00cf.v:201-204), as one region update: the class keeps Compl0 because the new
   run adds exactly cnt records and cnt * class_size c carved bytes. *)
Lemma WfP_cf_carve : forall U pp cc bb s c hs,
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
1 <= (rg_mapped_user (reg s c) - rg_alloc_user (reg s c)) / class_size c ->
4 * (fa_len (rg_free (reg s c)) + (rg_mapped_user (reg s c) - rg_alloc_user (reg s c)) / class_size c) <= rg_mapped_fa (reg s c) ->
Forall (fun h => h = (EXH_HOLE, 0)) hs -> NoDup hs ->
WfP_cf U pp cc bb (upd_reg c (mkRegion (rg_mapped_user (reg s c))
(rg_alloc_user (reg s c) + (rg_mapped_user (reg s c) - rg_alloc_user (reg s c)) / class_size c * class_size c)
(rg_mapped_fa (reg s c))
(FRun (rg_alloc_user (reg s c)) ((rg_mapped_user (reg s c) - rg_alloc_user (reg s c)) / class_size c) :: rg_free (reg s c)) hs) s).
Proof.
intros U pp cc bb s c hs W Hc Hcnt Hfa Hh Hnd.
pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (cls_ok_cf_populate c (reg s c) _ _ _ _ C Ksz) as CP. cbv zeta in CP. specialize (CP Hcnt Hfa).
pose proof (cls_ok_cf_set_holes _ _ _ _ _ _ hs CP Hh Hnd) as CH. cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free] in CH.
pose proof (wfc_slack _ _ _ _ _ W) as SL. pose proof (wfc_compl0 _ _ _ _ _ W c Hc) as H0. unfold cdef, class_elems in H0.
set (cnt := (rg_mapped_user (reg s c) - rg_alloc_user (reg s c)) / class_size c) in *.
unfold upd_reg. eapply WfP_cf_set_region; [exact W | exact Hc | exact CH | lia | |].
- cbn [rg_mapped_user]. pose proof (wfc_prim_ev _ _ _ _ _ W). lia.
- cbn [rg_alloc_user rg_free]. rewrite fa_elems_cons_run, !length_app, run_elems_length.
rewrite !length_app in H0. rewrite !Nat2Z.inj_add in *. rewrite Z2Nat.id by lia. nia.
Qed.

Section MAPC.
Context {ci : CfImg}.

(* map_more_user_cf in all its arms, over atok_cf: the map fits (YG06cf's map_more_user_cf_ok_tok), the
   class's byte is already set (same), the class is full and the byte clear (the errbuf report, then
   set_exh_cf), or no map is needed. ok = false costs one unit of cc (the report may append the size
   entry); ok = true leaves the state but region c untouched. *)
Definition map_postx_cf (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r' s0, errb_frame s s0 /\ st_nev s <= st_nev s0 /\ secs_ext_cf s s0 /\ s' = upd_reg c r' s0 /\
WfP_cf U (pp - 1) (if ok then cc else cc - 1) bb s' /\
rg_alloc_user r' = rg_alloc_user (reg s c) /\ rg_free r' = rg_free (reg s c) /\ rg_mapped_fa r' = rg_mapped_fa (reg s c) /\
(ok = true -> s0 = s /\ rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user r') /\
(ok = false -> ns = false \/ existsb (fun h => fst h =? EXH_HOLE) (rg_holes r') = true).

Lemma map_more_user_cf_okx : forall U pp cc bb s c need ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= cc -> 0 < need * class_size c <= kMaxSize ->
(c = kBatchClass -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) -> ERRB_ROOM s ->
atok_cf ns (map_more_user_cf c need s) (map_postx_cf U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hcc Hneed H24 Hroom.
pose proof (wfc_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_cf_len_regions; [exact W | lia]).
assert (CONV : forall b ok s', map_post_cf U pp cc bb s c need b (ok, s') -> map_postx_cf U pp cc bb s c need b (ok, s')).
{ intros b ok s' (r' & -> & W' & A & F & M & _ & OKt & OKf). exists r', s.
split; [apply errb_frame_refl|]. split; [lia|]. split; [apply secs_ext_cf_refl|]. split; [reflexivity|].
split; [destruct ok; cbv iota; [exact W' | eapply WfP_cf_weaken; [exact W' | lia | lia | lia]]|].
split; [exact A|]. split; [exact F|]. split; [exact M|].
split; [intros E; split; [reflexivity | exact (OKt E)]|].
intros E. destruct (OKf E) as [N | [_ X]]; [left; exact N | right; exact X]. }
assert (VIA : rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset \/ exh_mem_cf s c = true ->
atok_cf ns (map_more_user_cf c need s) (map_postx_cf U pp cc bb s c need)).
{ intros Hf. eapply atok_cf_mono; [|exact (map_more_user_cf_ok_tok U pp cc bb s c need ns W Hc Hpp Hneed H24 Hf)].
intros b [ok s'] HP. exact (CONV b ok s' HP). }
destruct (Z.eq_dec c kBatchClass) as [E24|N24]; [apply VIA; left; exact (H24 E24)|].
destruct (Z.le_gt_cases (rg_mapped_user (reg s c) + kUserMapSize) kFreeArrayOffset) as [Hfit|Hover]; [apply VIA; left; exact Hfit|].
destruct (exh_mem_cf s c) eqn:Ex; [apply VIA; right; reflexivity|].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [Hlt|Hge].
- apply (map_more_user_cf_full_tok U pp cc bb s c need ns _ W Hc N24 Hneed Hlt Hover).
apply atok_cf_bind. eapply atok_cf_mono; [|apply (errb_report_cf_ok U pp cc bb s c ns W Hcc Hroom)].
intros b [[] s1] (W1 & F1 & N1 & X1). cbv beta in *. cbn [fst snd] in *.
assert (REG1 : reg s1 c = reg s c) by (rewrite F1; reflexivity).
eapply atok_cf_mono; [|apply (set_exh_ret_cf_tok U pp (cc - 1) bb s1 c b W1 Hc)].
intros b2 [ok s2] (Eok & r' & -> & W2 & E1 & E2 & E3 & E4 & EX). subst ok.
exists r', s1. split; [exact F1|]. split; [exact N1|]. split; [exact X1|]. split; [reflexivity|].
split; [cbv iota; eapply WfP_cf_weaken; [exact W2 | lia | lia | lia]|].
rewrite REG1 in E2, E3, E4. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
split; [intros E; discriminate E | intros _; right; exact EX].
- unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbv beta iota.
apply atok_cf_bind. apply atok_cf_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [Hlt|_]; [lia|].
apply atok_cf_ret. exists (reg s c), s. split; [apply errb_frame_refl|]. split; [lia|]. split; [apply secs_ext_cf_refl|].
split; [symmetry; apply upd_reg_same; [lia | exact HL]|].
split; [cbv iota; eapply WfP_cf_weaken; [exact W | lia | lia | lia]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros _; split; [reflexivity | exact Hge] | intros E; discriminate E].
Qed.

(* cgif's populate_postx / populate_okx (YG06.v:320-397) for populate_cf. *)
Definition populate_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r' s0, errb_frame s s0 /\ st_nev s <= st_nev s0 /\ secs_ext_cf s s0 /\ s' = upd_reg c r' s0 /\
WfP_cf U (pp - 1) (if ok then cc else cc - 1) bb s' /\
(ok = true -> s0 = s /\ fa_len (rg_free (reg s c)) + need <= fa_len (rg_free r')) /\
(ok = false -> ns = false \/ existsb (fun h => fst h =? EXH_HOLE) (rg_holes r') = true).

Lemma populate_cf_ok : forall U pp cc bb s c need ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= cc -> 1 <= need ->
need * class_size c <= kMaxSize -> fa_len (rg_free (reg s c)) <= 8 ->
(c = kBatchClass -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) -> ERRB_ROOM s ->
atok_cf ns (populate_cf c need s) (populate_post_cf U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hcc Hneed Hnsz Hfl8 H24 Hroom.
pose proof (class_ok c Hc) as (Ksz & _). pose proof (class_size_32 c Hc) as K32.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_cf_len_regions; [exact W | lia]).
pose proof (wfc_slack _ _ _ _ _ W) as SL.
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C0. unfold wf_class_cf in C0.
pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C0)) as FL0.
(* the carve after a successful map, in both arms; clr is populate_cf's clear_exh_cf *)
assert (CARVE : forall (clr : bool) ns1 r1,
WfP_cf U (pp - 1) cc bb (upd_reg c r1 s) ->
rg_alloc_user r1 = rg_alloc_user (reg s c) -> rg_free r1 = rg_free (reg s c) -> rg_mapped_fa r1 = rg_mapped_fa (reg s c) ->
rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user r1 ->
atok_cf ns1 ((r <- get_region c ;;
ok2 <- ensure_free_array c (fa_len (rg_free r) + (rg_mapped_user r - rg_alloc_user r) / class_size c) false ;;
if negb ok2 then ret false
else r2 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + (rg_mapped_user r - rg_alloc_user r) / class_size c * class_size c)
(rg_mapped_fa r2) (FRun (rg_alloc_user r2) ((rg_mapped_user r - rg_alloc_user r) / class_size c) :: rg_free r2) (rg_holes r2)) ;;
(if clr then (clear_exh_cf c ;; ret true) else ret true)) (upd_reg c r1 s))
(populate_post_cf U pp cc bb s c need)).
{ intros clr ns1 r1 W1 A1 F1 M1 OK1.
apply atok_cf_bind. apply atok_cf_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
pose proof (wfc_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite reg_upd_reg in C1 by (lia || exact HL).
set (cnt := (rg_mapped_user r1 - rg_alloc_user r1) / class_size c).
assert (Hcnt1 : need <= cnt). { subst cnt. apply Z.div_le_lower_bound; [lia|]. rewrite A1. nia. }
assert (Hcnt4 : cnt <= 10240).
{ pose proof (wrc_carved _ _ _ _ _ _ C1) as CV. unfold kUserMapSize, kMaxSize in *.
assert (cnt <= (262144 + 65536) / class_size c) by (subst cnt; apply Z.div_le_mono; lia).
assert ((262144 + 65536) / class_size c <= (262144 + 65536) / 32) by (apply Z.div_le_compat_l; lia).
change ((262144 + 65536) / 32) with 10240 in *. lia. }
pose proof (wfc_slack _ _ _ _ _ W1) as SL1.
apply atok_cf_bind.
eapply atok_cf_mono; [|apply (ensure_free_array_ok_cf_tok U (pp - 1) cc bb (upd_reg c r1 s) c (fa_len (rg_free r1) + cnt) false ns1 W1 Hc)].
2:{ rewrite reg_upd_reg by (lia || exact HL). lia. }
2:{ rewrite reg_upd_reg by (lia || exact HL). pose proof (wrc_fa _ _ _ _ _ _ C1) as [Fa0 _]. rewrite F1. unfold kFreeArrayMapSize. lia. }
2:{ rewrite F1. unfold kFreeArrayMax. lia. }
intros ns2 [ok2 s2] (r2 & -> & W2 & M2 & A2 & F2 & FA2 & OK2 & NS2). cbn [fst snd].
rewrite upd_reg_upd_reg in *. rewrite reg_upd_reg in M2, A2, F2, FA2 by (lia || exact HL).
destruct ok2; cbn [negb].
2:{ apply atok_cf_ret. exists r2, s. split; [apply errb_frame_refl|]. split; [lia|]. split; [apply secs_ext_cf_refl|].
split; [reflexivity|]. split; [cbv iota; eapply WfP_cf_weaken; [exact W2 | lia | lia | lia]|].
split; [intros E; discriminate E | intros _; left; exact (proj1 (NS2 eq_refl))]. }
specialize (OK2 eq_refl).
assert (HL2 : (Z.to_nat c < length (st_regions (upd_reg c r2 s)))%nat) by (unfold upd_reg; cbn; rewrite zupd_length; exact HL).
apply atok_cf_bind. apply atok_cf_get_region. rewrite reg_upd_reg by (lia || exact HL2). cbn [fst snd].
pose proof (wfc_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class_cf in C2. rewrite reg_upd_reg in C2 by (lia || exact HL2).
pose proof (wrc_holes _ _ _ _ _ _ C2) as [Hh2 Hnd2].
assert (Ecnt : (rg_mapped_user r2 - rg_alloc_user r2) / class_size c = cnt) by (subst cnt; rewrite M2, A2; reflexivity).
assert (CV : forall hs, Forall (fun h => h = (EXH_HOLE, 0)) hs -> NoDup hs ->
WfP_cf U (pp - 1) cc bb (upd_reg c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + cnt * class_size c) (rg_mapped_fa r2)
(FRun (rg_alloc_user r2) cnt :: rg_free r2) hs) s)).
{ intros hs Hh Hnd. pose proof (WfP_cf_carve U (pp - 1) cc bb (upd_reg c r2 s) c hs W2 Hc) as WC.
rewrite !reg_upd_reg in WC by (lia || exact HL || exact HL2). rewrite Ecnt in WC. rewrite upd_reg_upd_reg in WC.
apply WC; [lia | rewrite F2; lia | exact Hh | exact Hnd]. }
assert (POST : forall hs, Forall (fun h => h = (EXH_HOLE, 0)) hs -> NoDup hs ->
populate_post_cf U pp cc bb s c need ns2 (true, upd_reg c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + cnt * class_size c)
(rg_mapped_fa r2) (FRun (rg_alloc_user r2) cnt :: rg_free r2) hs) s)).
{ intros hs Hh Hnd. eexists. exists s. split; [apply errb_frame_refl|]. split; [lia|]. split; [apply secs_ext_cf_refl|].
split; [reflexivity|]. split; [cbv iota; exact (CV hs Hh Hnd)|].
split; [intros _; split; [reflexivity | cbn [rg_free fa_len]; rewrite F2, F1; lia] | intros E; discriminate E]. }
apply atok_cf_bind. apply atok_cf_set_region. cbn [fst snd]. rewrite upd_reg_upd_reg.
destruct clr.
- apply atok_cf_bind. unfold clear_exh_cf. apply atok_cf_bind. apply atok_cf_get_region. cbn [fst snd].
rewrite reg_upd_reg by (lia || exact HL).
apply atok_cf_set_region. cbn [fst snd rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes]. apply atok_cf_ret. rewrite upd_reg_upd_reg.
apply POST; [apply exh_holes_del; exact Hh2 | apply NoDup_del_hole; exact Hnd2].
- apply atok_cf_ret. apply POST; [exact Hh2 | exact Hnd2]. }
unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E24|N24]; cbv beta iota zeta.
- (* class kBatchClass: cgif's populate, whose map is map_more_user_cf's first arm *)
unfold populate. cbv beta zeta. apply atok_cf_bind.
replace (map_more_user c need) with (map_more_user_cf c need)
by (unfold map_more_user_cf; destruct (Z.eqb_spec c kBatchClass); [reflexivity | contradiction]).
eapply atok_cf_mono; [|apply (map_more_user_cf_okx U pp cc bb s c need ns W Hc Hpp Hcc ltac:(nia) H24 Hroom)].
intros ns1 [ok s1] (r1 & s0 & F0 & N0 & X0 & -> & W1 & A1 & F1 & M1 & OKt & OKf). cbn [fst snd].
destruct ok; cbn [negb].
+ destruct (OKt eq_refl) as [-> MM]. exact (CARVE false ns1 r1 W1 A1 F1 M1 MM).
+ apply atok_cf_ret. exists r1, s0. split; [exact F0|]. split; [exact N0|]. split; [exact X0|]. split; [reflexivity|].
split; [exact W1|]. split; [intros E; discriminate E | intros _; exact (OKf eq_refl)].
- apply atok_cf_bind.
eapply atok_cf_mono; [|apply (map_more_user_cf_okx U pp cc bb s c need ns W Hc Hpp Hcc ltac:(nia) H24 Hroom)].
intros ns1 [ok s1] (r1 & s0 & F0 & N0 & X0 & -> & W1 & A1 & F1 & M1 & OKt & OKf). cbn [fst snd].
destruct ok; cbn [negb].
+ destruct (OKt eq_refl) as [-> MM]. exact (CARVE true ns1 r1 W1 A1 F1 M1 MM).
+ apply atok_cf_ret. exists r1, s0. split; [exact F0|]. split; [exact N0|]. split; [exact X0|]. split; [reflexivity|].
split; [exact W1|]. split; [intros E; discriminate E | intros _; exact (OKf eq_refl)].
Qed.

(* cgif's gfa_post / get_from_allocator_okx (YG06.v:420-474) for get_from_allocator_cf. *)
Definition gfa_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c n : Z) (ns : bool) (res : option (list Z) * astate) : Prop :=
let (o, s') := res in
match o with
| None => exists r' s0, errb_frame s s0 /\ st_nev s <= st_nev s0 /\ secs_ext_cf s s0 /\ s' = upd_reg c r' s0 /\
WfP_cf U (pp - 1) (cc - 1) bb s' /\ (ns = false \/ existsb (fun h => fst h =? EXH_HOLE) (rg_holes r') = true)
| Some tops => exists r2 rest, WfP_cf U (pp - 1) cc bb (upd_reg c r2 s) /\
s' = upd_reg c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)) s /\
runs_ok rest /\ fa_elems (class_size c) (rg_free r2) = tops ++ fa_elems (class_size c) rest /\
Z.of_nat (length tops) = n /\ fa_len rest = fa_len (rg_free r2) - n
end.

Lemma get_from_allocator_cf_ok : forall U pp cc bb s c n ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= cc -> 1 <= n -> n * class_size c <= kMaxSize -> n <= 8 ->
(c = kBatchClass -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) -> ERRB_ROOM s ->
atok_cf ns (get_from_allocator_cf c n s) (gfa_post_cf U pp cc bb s c n).
Proof.
intros U pp cc bb s c n ns W Hc Hpp Hcc Hn Hnsz Hn8 H24 Hroom.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_cf_len_regions; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
pose proof (class_ok c Hc) as (Ksz & _). pose proof (wfc_slack _ _ _ _ _ W) as SL.
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C0. unfold wf_class_cf in C0.
pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C0)) as FL0.
unfold get_from_allocator_cf. apply atok_cf_bind. apply atok_cf_get_region. cbn [fst snd].
apply atok_cf_bind.
apply (atok_cf_mono _ _ (fun ns1 (res : bool * astate) => let (ok, s1) := res in
exists r1 s0, errb_frame s s0 /\ st_nev s <= st_nev s0 /\ secs_ext_cf s s0 /\ s1 = upd_reg c r1 s0 /\
WfP_cf U (pp - 1) (if ok then cc else cc - 1) bb s1 /\
(ok = true -> s0 = s /\ n <= fa_len (rg_free r1)) /\
(ok = false -> ns1 = false \/ existsb (fun h => fst h =? EXH_HOLE) (rg_holes r1) = true))).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg s c))) n) as [Hlt|Hge].
- eapply atok_cf_mono; [|apply (populate_cf_ok U pp cc bb s c (n - fa_len (rg_free (reg s c))) ns W Hc Hpp Hcc); [lia | nia | lia | exact H24 | exact Hroom]].
intros ns1 [ok s1] (r1 & s0 & F0 & N0 & X0 & -> & W1 & OKt & OKf). exists r1, s0.
split; [exact F0|]. split; [exact N0|]. split; [exact X0|]. split; [reflexivity|]. split; [exact W1|].
split; [intros E; destruct (OKt E) as [-> HF]; split; [reflexivity | lia] | exact OKf].
- apply atok_cf_ret. exists (reg s c), s. rewrite ES. split; [apply errb_frame_refl|]. split; [lia|]. split; [apply secs_ext_cf_refl|].
split; [reflexivity|]. split; [cbv iota; eapply WfP_cf_weaken; [exact W | lia | lia | lia]|].
split; [intros _; split; [reflexivity | lia] | intros E; discriminate E]. }
intros ns1 [ok s1] (r1 & s0 & F0 & N0 & X0 & -> & W1 & OKt & OKf). cbn [fst snd].
destruct ok; cbn [negb].
2:{ apply atok_cf_ret. exists r1, s0. split; [exact F0|]. split; [exact N0|]. split; [exact X0|]. split; [reflexivity|].
split; [exact W1 | exact (OKf eq_refl)]. }
destruct (OKt eq_refl) as [-> OK1].
apply atok_cf_bind. apply atok_cf_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
destruct (Z.ltb_spec (fa_len (rg_free r1)) n) as [Hlt|_]; [lia|].
pose proof (wfc_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite reg_upd_reg in C1 by (lia || exact HL).
pose proof (wrc_runs _ _ _ _ _ _ C1) as R1.
destruct (fa_pop_n_some 10000 (class_size c) n (rg_free r1) [] R1) as (tops & rest & Ep); [lia | change (Z.of_nat 10000) with 10000; lia |].
assert (Hn0 : 0 <= n) by lia.
rewrite Ep. destruct (fa_pop_n_spec _ _ _ _ _ _ _ R1 Hn0 Ep) as (E1 & E2 & E3 & E4). cbn [rev app length] in E1, E4.
apply atok_cf_bind. apply atok_cf_set_region. cbn [fst snd]. apply atok_cf_ret.
exists r1, rest. rewrite upd_reg_upd_reg. split; [exact W1|]. split; [reflexivity|]. split; [exact E3|]. split; [exact E1|].
split; [lia | exact E2].
Qed.

(* cache_alloc_cf (YG00cf.v:232-241). Some names the state just BEFORE the pop: the popped record is
   in no list of the class until malloc_cf stores it in its chunk (WfP_cf_pop_add_prim below). None: the
   refill was refused (ns = false) or the class is full (its byte is set), and the cc unit is spent. *)
Definition cache_alloc_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (res : option Z * astate) : Prop :=
let (o, s') := res in
st_cache_inited s' = true /\ regs_only_cf s s' /\
match o with
| None => WfP_cf U (pp - 1) (cc - 1) bb s' /\ (ns = false \/ exh_mem_cf s' c = true)
| Some off => exists s0 l, WfP_cf U (pp - 1) cc bb s0 /\ regs_only_cf s s0 /\ st_cache_inited s0 = true /\
pc_chunks (cache s0 c) = l /\ l <> [] /\ off = region_off c + last l 0 /\
s' = upd_pc c (mkPC (pc_max (cache s0 c)) (removelast l)) s0
end.

Lemma cache_alloc_cf_ok : forall U pp cc bb s c ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= cc ->
(c = kBatchClass -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) -> ERRB_ROOM s ->
atok_cf ns (cache_alloc_cf c s) (cache_alloc_post_cf U pp cc bb s c).
Proof.
intros U pp cc bb s c ns W Hc Hpp Hcc H24 Hroom.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs).
unfold cache_alloc_cf. apply atok_cf_bind. unfold init_cache_if_needed. apply atok_cf_bind. apply atok_cf_get. cbn [fst snd].
assert (STEP1 : forall s1, WfP_cf U pp cc bb s1 -> st_cache_inited s1 = true -> regs_only_cf s s1 ->
st_regions s1 = st_regions s -> st_secs s1 = st_secs s ->
atok_cf ns ((refill_if_empty_cf c ;; p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| z :: l0 => set_pc c (mkPC (pc_max p) (removelast (z :: l0))) ;; ret (Some (region_off c + last (z :: l0) 0))
end) s1) (cache_alloc_post_cf U pp cc bb s c)).
2:{ destruct (st_cache_inited s) eqn:Ei.
- apply atok_cf_ret. exact (STEP1 s W Ei (regs_only_cf_refl s) eq_refl eq_refl).
- apply atok_cf_put. apply STEP1; [apply WfP_cf_init_caches; [exact W | exact Ei] | reflexivity | exact (regs_only_cf_refl s) | reflexivity | reflexivity]. }
intros s1 W1 Hi1 RO1 ER1 ES1.
assert (HL : (Z.to_nat c < length (st_regions s1))%nat) by (eapply WfP_cf_len_regions; [exact W1 | lia]).
assert (HLc : (Z.to_nat c < length (st_cache s1))%nat) by (eapply WfP_cf_len_cache; [exact W1 | lia]).
pose proof (wfc_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite Hi1 in C1.
pose proof (wrc_cache _ _ _ _ _ _ C1) as [PM1 PL1].
assert (REG1 : forall c', reg s1 c' = reg s c') by (intros c'; unfold reg; rewrite ER1; reflexivity).
assert (ROOM1 : ERRB_ROOM s1) by (unfold ERRB_ROOM, errb_size_cf in *; rewrite ES1; exact Hroom).
assert (H241 : c = kBatchClass -> rg_mapped_user (reg s1 c) + kUserMapSize <= kFreeArrayOffset) by (rewrite REG1; exact H24).
pose proof (wfc_slack _ _ _ _ _ W1) as SL1.
assert (POP : forall ns2 s2, st_cache_inited s2 = true -> regs_only_cf s s2 ->
(pc_chunks (cache s2 c) <> [] -> WfP_cf U (pp - 1) cc bb s2) ->
(pc_chunks (cache s2 c) = [] -> WfP_cf U (pp - 1) (cc - 1) bb s2 /\ (ns2 = false \/ exh_mem_cf s2 c = true)) ->
atok_cf ns2 ((p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| z :: l0 => set_pc c (mkPC (pc_max p) (removelast (z :: l0))) ;; ret (Some (region_off c + last (z :: l0) 0))
end) s2) (cache_alloc_post_cf U pp cc bb s c)).
{ intros ns2 s2 Hi2 RO2 HW HN. apply atok_cf_bind. apply atok_cf_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|o l] eqn:El.
- apply atok_cf_ret. unfold cache_alloc_post_cf. destruct (HN eq_refl) as [W3 NS].
split; [exact Hi2|]. split; [exact RO2|]. split; [exact W3 | exact NS].
- apply atok_cf_bind. apply atok_cf_set_pc. cbn [fst snd]. apply atok_cf_ret. unfold cache_alloc_post_cf.
split; [exact Hi2|]. split; [exact RO2|].
exists s2, (o :: l). split; [apply HW; discriminate|]. split; [exact RO2|]. split; [exact Hi2|].
split; [exact El|]. split; [discriminate|]. split; reflexivity. }
apply atok_cf_bind. unfold refill_if_empty_cf. apply atok_cf_bind. apply atok_cf_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s1 c)) as [|o l] eqn:El.
- rewrite PM1. apply atok_cf_bind.
assert (N1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (N8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
eapply atok_cf_mono; [|apply (get_from_allocator_cf_ok U pp cc bb s1 c (max_cached c / 2) ns W1 Hc Hpp Hcc N1 Kmcs N8 H241 ROOM1)].
intros ns1 [got s2] Hg. cbn [fst snd]. destruct got as [tops|].
+ destruct Hg as (r2 & rest & W2 & -> & Hruns & Hel & Hlen & Hfl).
apply atok_cf_set_pc. cbn [fst snd].
set (r' := mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)).
pose proof (wfc_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class_cf in C2.
rewrite reg_upd_reg in C2 by (lia || exact HL). change (cache (upd_reg c r2 s1) c) with (cache s1 c) in C2.
change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1) in C2. rewrite Hi1 in C2.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c) in C2. change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c) in C2.
assert (W3 : WfP_cf U (pp - 1) cc bb (upd_pc c (mkPC (max_cached c) (cache_fill_order tops)) (upd_reg c r' s1))).
{ rewrite <- (upd_reg_upd_reg c r2 r' s1).
eapply (WfP_cf_set_region_pc U (pp - 1) cc bb (upd_reg c r2 s1) c); [exact W2 | exact Hc | | lia | |].
- change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1). rewrite Hi1.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c). change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c).
eapply (cls_ok_cf_repart c r2 (cache s1 c) true _ _ r' _ true _ _ []); try exact C2; try reflexivity.
+ exact Hruns.
+ subst r'. cbnr. pose proof (wrc_fa_len _ _ _ _ _ _ C2). lia.
+ cbn [pc_max pc_chunks]. split; [reflexivity|]. unfold cache_fill_order. rewrite length_rev. lia.
+ subst r'. cbnr. rewrite Hel, El. unfold cache_fill_order. cbn [pc_chunks app].
pose proof (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs s1 c) (batch_offs s1 c) tops) as PP. cbn [app] in PP. exact PP.
- rewrite reg_upd_reg by (lia || exact HL). subst r'. cbnr. pose proof (wfc_prim_ev _ _ _ _ _ W2) as PE. unfold kUserMapSize in *. lia.
- pose proof (wfc_compl0 _ _ _ _ _ W2 c Hc) as H0. unfold cdef, class_elems in H0. rewrite reg_upd_reg in H0 by (lia || exact HL).
change (cache (upd_reg c r2 s1) c) with (cache s1 c) in H0.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c) in H0 |- *.
change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c) in H0 |- *.
rewrite El, Hel in H0. subst r'. cbn [rg_alloc_user rg_free pc_chunks] in *. unfold cache_fill_order.
rewrite !length_app, length_rev in *. cbn [length] in H0. nia. }
eapply (POP ns1); [exact Hi1 | exact RO1 | intros _; exact W3 |].
intros E. exfalso. unfold upd_pc in E. rewrite cache_upd_same in E by (lia || exact HLc). cbn [pc_chunks] in E.
unfold cache_fill_order in E. apply (f_equal (@length Z)) in E. rewrite length_rev in E. cbn in E. lia.
+ destruct Hg as (r' & s0 & F0 & N0 & X0 & -> & W2 & NS). apply atok_cf_ret. cbn [fst snd].
eapply (POP ns1).
* rewrite F0. exact Hi1.
* exact (regs_only_cf_trans _ _ _ RO1 (regs_only_cf_frame _ _ F0 N0 X0)).
* intros Hne. exfalso. apply Hne. change (cache (upd_reg c r' s0) c) with (cache s0 c). rewrite F0. exact El.
* intros _. split; [exact W2|]. destruct NS as [NS|NS]; [left; exact NS|]. right. unfold exh_mem_cf.
rewrite reg_upd_reg; [exact NS | lia | rewrite F0; exact HL].
- apply atok_cf_ret. cbn [fst snd].
eapply (POP ns); [exact Hi1 | exact RO1 | intros _; eapply WfP_cf_weaken; [exact W1 | lia | lia | lia] |].
intros E. rewrite El in E. discriminate E.
Qed.
End MAPC.

(* The primary arm's last step: the record popped from the cache (cache_alloc_cf's Some) becomes the new
   allocated chunk's offset, so the class's records are only repartitioned (cache -> chunk) and Compl0
   holds again. cgif's pop_ok (YG06.v:611), cls_ok_add_ko (:239) and WfP_add_prim_chunk (YG02.v:309) in one
   step, since the state between them is not a WfP_cf state. The chunk count is paid by one unit of cc. *)
Lemma WfP_cf_pop_add_prim : forall U pp cc bb s c l n d,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> st_cache_inited s = true -> pc_chunks (cache s c) = l -> l <> [] ->
1 <= cc -> 0 <= n < cf_malloc_max -> from_primary n = true -> chunk_class n = c -> blocks_bytes s + n <= LIVE_MAX ->
depot_fits U d ->
0 <= last l 0 < rg_alloc_user (reg s c) /\ last l 0 mod class_size c = 0 /\ last l 0 < kFreeArrayOffset /\
~ In (PPrim (region_off c + last l 0)) (map ck_beg (st_chunks s)) /\
WfP_cf U pp (cc - 1) bb (set_chunks (st_chunks s ++ [mkChunk (PPrim (region_off c + last l 0)) n CAllocated])
(set_depot d (upd_pc c (mkPC (pc_max (cache s c)) (removelast l)) s))).
Proof.
intros U pp cc bb s c l n d W Hc Hi Hl Hne Hcc Hn Hp Hcn Hlive Hd.
assert (L1 : (1 <= length l)%nat) by (destruct l; [contradiction | cbn; lia]).
assert (HLc : (Z.to_nat c < length (st_cache s))%nat) by (eapply WfP_cf_len_cache; [exact W | lia]).
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C. rewrite Hi in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as [PM PL].
pose proof (mapped_bound_cf U pp cc bb s c W Hc) as MB. pose proof (wrc_alloc _ _ _ _ _ _ C) as AL.
assert (Hxin : In (last l 0) (pc_chunks (cache s c))) by (rewrite Hl; apply last_in_ne; exact Hne).
assert (HX : 0 <= last l 0 < rg_alloc_user (reg s c) /\ last l 0 mod class_size c = 0).
{ apply (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ C)). apply in_app_iff. right. apply in_app_iff. left. exact Hxin. }
assert (Hxk : ~ In (last l 0) (chunk_offs s c)).
{ intros Hin. pose proof (wrc_nodup _ _ _ _ _ _ C) as ND. rewrite Hl in ND, Hxin.
apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & D).
apply (D _ Hxin). apply in_app_iff. left. exact Hin. }
set (x := last l 0) in *. set (p' := mkPC (pc_max (cache s c)) (removelast l)).
set (k := mkChunk (PPrim (region_off c + x)) n CAllocated).
assert (Hx32 : 0 <= x < 2 ^ 32) by (unfold kFreeArrayOffset in *; lia).
assert (Hfresh : ~ In (PPrim (region_off c + x)) (map ck_beg (st_chunks s))).
{ intros Hin. apply in_map_iff in Hin as (k' & Hb & Hk'). apply Hxk.
pose proof (In_chunk_offs s k' _ Hk' Hb) as H. rewrite prim_class_region_off in H by lia.
replace (region_off c + x - region_off c) with x in H by lia. exact H. }
assert (HP : Permutation (fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c)
([] ++ fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks p' ++ (chunk_offs s c ++ [x]) ++ batch_offs s c)).
{ subst p'. cbn [pc_chunks app]. rewrite Hl. rewrite <- (removelast_app_last l 0 Hne) at 1. fold x.
apply Permutation_app_head. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_middle. }
assert (C' : cls_ok_cf c (reg s c) p' true (chunk_offs s c ++ [x]) (batch_offs s c)).
{ eapply (cls_ok_cf_repart c _ _ true _ _ _ _ true _ _ []); try exact C; try reflexivity.
- exact (wrc_runs _ _ _ _ _ _ C).
- exact (wrc_fa_len _ _ _ _ _ _ C).
- subst p'. cbn [pc_max pc_chunks]. split; [exact PM|]. rewrite removelast_length by exact Hne. rewrite Hl in PL. lia.
- exact HP. }
set (S' := set_chunks (st_chunks s ++ [k]) (set_depot d (upd_pc c p' s))).
assert (CO : forall c', chunk_offs S' c' = chunk_offs s c' ++ (if c =? c' then [x] else [])).
{ intros c'. subst S'. unfold chunk_offs. cbn [st_chunks set_chunks]. rewrite flat_map_app. f_equal.
subst k. cbn [flat_map ck_beg]. rewrite app_nil_r. rewrite prim_class_region_off by lia.
destruct (Z.eqb_spec c c') as [<-|Hne']; [|reflexivity].
replace (region_off c + x - region_off c) with x by lia. reflexivity. }
assert (CE : forall c', 1 <= c' <= 31 -> length (class_elems S' c') = length (class_elems s c')).
{ intros c' Hc'. unfold class_elems. rewrite CO.
change (reg S' c') with (reg s c'). change (batch_offs S' c') with (batch_offs s c').
change (cache S' c') with (cache (upd_pc c p' s) c').
destruct (Z.eqb_spec c c') as [<-|Hne'].
- rewrite cache_upd_pc by (lia || exact HLc). subst p'. cbn [pc_chunks].
rewrite Hl, !length_app, removelast_length by exact Hne. cbn [length]. lia.
- unfold upd_pc. rewrite cache_upd_other by lia. rewrite app_nil_r. reflexivity. }
split; [exact (proj1 HX)|]. split; [exact (proj2 HX)|]. split; [lia|]. split; [exact Hfresh|].
pose proof (wfc_slack _ _ _ _ _ W) as SL.
constructor.
- exact (wfc_len_regions _ _ _ _ _ W).
- subst S'. unfold upd_pc. cbn [st_cache set_chunks set_depot set_cache]. rewrite zupd_length. exact (wfc_len_cache _ _ _ _ _ W).
- exact (wfc_reg0 _ _ _ _ _ W).
- intros c' Hc'. unfold wf_class_cf. rewrite CO.
change (reg S' c') with (reg s c'). change (st_cache_inited S') with (st_cache_inited s).
change (batch_offs S' c') with (batch_offs s c'). change (cache S' c') with (cache (upd_pc c p' s) c').
destruct (Z.eqb_spec c c') as [<-|Hne'].
+ rewrite cache_upd_pc by (lia || exact HLc). rewrite Hi. exact C'.
+ unfold upd_pc. rewrite cache_upd_other by lia. rewrite app_nil_r. exact (wfc_classes _ _ _ _ _ W c' Hc').
- subst S'. cbn [st_chunks set_chunks]. apply Forall_app. split.
+ eapply Forall_impl; [|exact (wfc_chunks _ _ _ _ _ W)]. intros k0 H0. exact H0.
+ constructor; [|constructor]. unfold chunk_ok_cf. subst k. cbn [ck_req ck_beg]. split; [exact Hn|].
rewrite prim_class_region_off by lia. split; [exact Hp|]. split; [symmetry; exact Hcn|].
replace (region_off c + x - region_off c) with x by lia. lia.
- subst S'. cbn [st_chunks set_chunks]. rewrite map_app. cbn [map].
apply NoDup_app_iff. split; [exact (wfc_chunks_nodup _ _ _ _ _ W)|]. split; [repeat constructor; intros []|].
intros y Hy [<-|[]]. subst k. cbn [ck_beg] in Hy. exact (Hfresh Hy).
- subst S'. unfold upd_pc. cbn [st_chunks st_nev set_chunks set_depot set_cache]. rewrite length_app. cbn [length].
pose proof (wfc_chunks_ev _ _ _ _ _ W). lia.
- exact (wfc_prim_ev _ _ _ _ _ W).
- subst S'. change (blocks_bytes (set_chunks (st_chunks s ++ [k]) (set_depot d (upd_pc c p' s))))
with (blocks_bytes (set_chunks (st_chunks s ++ [k]) s)).
rewrite blocks_bytes_app1. subst k. cbn [is_alloc ck_state ck_req]. lia.
- pose proof (wfc_quarantine _ _ _ _ _ W) as Xq. quar_fields Xq. subst S'. unfold upd_pc.
constructor; cbn [st_qthread st_qglobal st_chunks set_chunks set_depot set_cache]; try assumption.
eapply Forall_impl; [|exact Qit]. intros k0 [Hk Hs]. split; [apply in_app_iff; left; exact Hk | exact Hs].
- exact (wfc_batches_ev _ _ _ _ _ W).
- pose proof (wfc_secondary _ _ _ _ _ W) as X. subst S'. unfold upd_pc.
pose proof (wsc_nodup _ X) as Snd. pose proof (wsc_arr_chunks _ X) as Sac. pose proof (wsc_arr_live _ X) as Sal.
pose proof (wsc_reserved _ X) as Sres. pose proof (wsc_reserved_al _ X) as Sral. pose proof (wsc_lens _ X) as Slen.
constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks set_depot set_cache]; try assumption.
intros r. rewrite Sac. split.
+ intros (k0 & Hk & Hb). exists k0. split; [apply in_app_iff; left; exact Hk | exact Hb].
+ intros (k0 & Hk & Hb). apply in_app_iff in Hk as [Hk|[<-|[]]]; [exists k0; auto | subst k; cbn in Hb; discriminate].
- apply (wf_fs_ext s); [reflexivity | exact (wfc_fakestack _ _ _ _ _ W)].
- exact Hd.
- exact (wfc_nev _ _ _ _ _ W).
- lia.
- exact (wfc_qinited _ _ _ _ _ W).
- pose proof (wfc_secs_ev _ _ _ _ _ W). change (st_secs S') with (st_secs s). change (st_nev S') with (st_nev s). lia.
- intros c' Hc'. unfold cdef. rewrite CE by exact Hc'. change (reg S' c') with (reg s c'). exact (wfc_compl0 _ _ _ _ _ W c' Hc').
- exact (wfc_sec_live _ _ _ _ _ W).
- apply (qsize_ext s); [first [reflexivity | (subst S'; reflexivity)] | first [reflexivity | (subst S'; reflexivity)] | exact (wfc_qsize _ _ _ _ _ W)].
Qed.
End CACHE.
