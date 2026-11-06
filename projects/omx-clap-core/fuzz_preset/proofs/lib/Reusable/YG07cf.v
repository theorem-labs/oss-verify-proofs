(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: WfP_cf_add_sec proves WfP_cf's new field wfc_qsize (the queues do not change). *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YG07cf.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), malloc_cf's law. cgif's YG07.v
   (malloc_gen :292, malloc_ok :470) restated over WfP_cf (YG01cf.v), atok_cf (YGcfTok.v) and malloc_cf
   (YG00cf.v), with the cache path of YG06bcf.v. malloc_gen_cf has NO event premise: cgif's regime_ok /
   aregime (YG07.v:294, :472) are gone, and with them the BigInv and mgrow conjuncts of its post (BigInv's
   Compl0 is a field of Wf_cf; mgrow fed the event budget, which the cf instance replaces by live state,
   YG08cf.v).
   The call premises are the live-state ones of the instance: Z.of_nat (length (st_sec_arr s)) <
   cf_sec_live_max (a secondary appends an entry), ERRB_ROOM (the class-full report may grow the errbuf) and
   batch_room_cf (class kBatchClass keeps cgif's map mcheck).
   malloc_post_cf is cgif's malloc_post (YG01.v:449-456) with Wf_cf, with `st_nev s + 1 <= st_nev s'` for the
   equation (the class-full report's errbuf map ticks) and secs_ext_cf for secs_ext (the report rewrites
   the errbuf control entries in place).
   The class-full arm returns PNull WITHOUT a refused request, so cgif's `fst r = PNull -> ns = false`
   (YG0u.v:24) becomes a disjunction with that arm's flag.
   The two event-keyed lemmas of YG07.v are NOT restated, because both are FALSE for this instance:
   - nrecZ_small (YG07.v:267), `nrecZ s c + 10248 <= 65536`: preset's class 17 carries up to 4.89e6 records
     and fuzz_reply's class 1 carries 63,352,651. Its one consumer, malloc_gen's BigP step (YG07.v:304-306,
     :370, :386), has no counterpart: BigP is not an invariant of the cf instance, and the free-array
     CAPACITY it stood for is nrec_bound_cf (YG01cf.v), `4 * records <= kFreeArrayMax`, from class_size c >= 32
     and rg_mapped_user <= kFreeArrayOffset. The populate step itself needs no record bound: one populate
     carves at most 10,240 records (YG06bcf.v, populate_cf_ok).
   - sec_arr_small (YG07.v:273), `length (st_sec_arr s) < kPtrArrayEntriesPerCommit` from st_nev <= EV_MAX.
     Its consumers use the field wfc_sec_live (sec_live_bound_cf, YG01cf.v), `<= cf_sec_live_max`, with
     CfParams' cf_sec_live_commit (cf_sec_live_max < kPtrArrayEntriesPerCommit) for the single commit.
   The state-only lemmas of YG07.v (depot_put_ok, nth_error_app_l, nth_error_lt, blocks_bytes_set,
   In_chunk_offs, prim_class_window, cdef_add_prim, blocks_set_chunks_app, needs_remap_secondary,
   secs_ext_app, the definitions depot_post and sec_alloc_post) do not mention Wf, so they are used from
   YG07.v as they are. depot_put_ok's atok transfers to atok_cf by atok_cf_of_atok (YGcfTok.v).
   cgif's YG07.v is NOT edited. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfTok YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG02cf YG06cf YG06bcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

Section YG07CF.
Context {cp : CfParams}.

(* cgif's WfP_set_depot (YG07.v:59). *)
Lemma WfP_cf_set_depot : forall U pp cc bb s d,
WfP_cf U pp cc bb s -> depot_fits U d -> WfP_cf U pp cc bb (set_depot d s).
Proof.
intros U pp cc bb s d W Hd. destruct W. constructor; try assumption.
- apply (wf_quar_ext s); [reflexivity | reflexivity | reflexivity | assumption].
- apply (wf_sec_cf_ext s); [reflexivity | reflexivity | reflexivity | reflexivity | assumption].
- apply (wf_fs_ext s); [reflexivity | assumption].
Qed.

(* cgif's chunk_ok_app_secs (YG07.v:69). *)
Lemma chunk_ok_cf_app_secs : forall s l k, chunk_ok_cf s k -> chunk_ok_cf (set_secs (st_secs s ++ l) s) k.
Proof.
intros s l k H. unfold chunk_ok_cf in *. destruct H as [H1 H2]. split; [exact H1|].
destruct (ck_beg k); try exact H2. destruct H2 as (A & B & sm & E & C). split; [exact A|]. split; [exact B|].
exists sm. cbn. rewrite nth_error_app_l by (eapply nth_error_lt; exact E). split; [exact E | exact C].
Qed.

(* cgif's sec_arr_length (YG07.v:77). *)
Lemma sec_arr_length_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> (length (st_sec_arr s) <= length (st_chunks s))%nat.
Proof.
intros U pp cc bb s W. pose proof (wfc_secondary _ _ _ _ _ W) as X.
pose proof (wsc_nodup _ X) as Snd. pose proof (wsc_arr_chunks _ X) as Sac.
rewrite <- (length_map (fun r => PSec r kPage) (st_sec_arr s)), <- (length_map ck_beg (st_chunks s)).
apply NoDup_incl_length.
- apply NoDup_map_NoDup_ForallPairs; [|exact Snd]. intros a b _ _ H. injection H. auto.
- intros p Hp. apply in_map_iff in Hp as (r & <- & Hr). apply Sac in Hr as (k & Hk & Hb). apply in_map_iff. exists k. auto.
Qed.

(* cgif's sec_map_size_range (YG07.v:85), with cf_malloc_max for MALLOC_MAX and cf_nob for SEC_LEN_MAX. *)
Lemma sec_map_size_range_cf : forall n, 0 <= n < cf_malloc_max -> 0 <= sec_map_size n <= cf_nob.
Proof. intros n Hn. pose proof (sec_map_size_nonneg n ltac:(lia)). pose proof (cf_sizes_ok n Hn). lia. Qed.

(* cgif's WfP_add_sec (YG07.v:95). The premise HSEC is cgif's sec_arr_small at the cf bound:
   `length (st_sec_arr s) < cf_sec_live_max`, which keeps wfc_sec_live after the append and, through
   cf_sec_live_commit, keeps the pointer array at its single commit. *)
Lemma WfP_cf_add_sec : forall U pp cc bb s n d res',
WfP_cf U pp cc bb s -> 1 <= cc -> 0 <= n < cf_malloc_max -> from_primary n = false -> blocks_bytes s + n <= LIVE_MAX ->
depot_fits U d ->
Z.of_nat (length (st_sec_arr s)) < cf_sec_live_max ->
((res' = st_sec_reserved s /\ Z.of_nat (length (st_sec_arr s)) < st_sec_reserved s) \/
(res' = st_sec_reserved s + kPtrArrayEntriesPerCommit /\ Z.of_nat (length (st_sec_arr s)) = st_sec_reserved s)) ->
let r := length (st_secs s) in
let sm := mkSec (sec_map_size n) (needed_size n) true in
WfP_cf U pp (cc - 1) bb
(set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated])
(set_depot d (set_sec_arr (st_sec_arr s ++ [r]) (set_sec_reserved res' (set_secs (st_secs s ++ [sm]) s))))).
Proof.
intros U pp cc bb s n d res' W Hcc Hn Hprim Hlive Hd HSEC Hres r sm.
pose proof (wfc_secondary _ _ _ _ _ W) as X.
pose proof (wsc_nodup _ X) as Snd. pose proof (wsc_arr_chunks _ X) as Sac. pose proof (wsc_arr_live _ X) as Sal.
pose proof (wsc_reserved _ X) as Sres. pose proof (wsc_reserved_al _ X) as Sral. pose proof (wsc_lens _ X) as Slen.
pose proof (wfc_chunks _ _ _ _ _ W) as Xck. pose proof cf_sec_live_commit as SLC.
assert (Hfresh : forall k, In k (st_chunks s) -> forall o, ck_beg k <> PSec r o).
{ intros k Hk o E. pose proof (proj1 (Forall_forall _ _) Xck k Hk) as [_ CK]. rewrite E in CK.
destruct CK as (_ & _ & sm' & Es & _). apply nth_error_lt in Es. subst r. lia. }
assert (Hr_notin : ~ In r (st_sec_arr s)).
{ intros Hin. apply Sac in Hin as (k & Hk & Hb). exact (Hfresh k Hk _ Hb). }
assert (Hce : forall c', class_elems (set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated])
(set_depot d (set_sec_arr (st_sec_arr s ++ [r]) (set_sec_reserved res' (set_secs (st_secs s ++ [sm]) s))))) c'
= class_elems s c').
{ intros c'. unfold class_elems, chunk_offs.
cbn [st_chunks st_regions st_cache st_qthread st_qglobal set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
rewrite flat_map_app. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity. }
constructor.
- exact (wfc_len_regions _ _ _ _ _ W).
- exact (wfc_len_cache _ _ _ _ _ W).
- exact (wfc_reg0 _ _ _ _ _ W).
- intros c' Hc'. unfold wf_class_cf.
change (chunk_offs ?[S] c') with (chunk_offs (set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated]) s) c').
rewrite chunk_offs_app. unfold chunk_offs at 2. cbn [st_chunks set_chunks flat_map ck_beg app]. rewrite app_nil_r.
exact (wfc_classes _ _ _ _ _ W c' Hc').
- cbn [st_chunks set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. apply Forall_app. split.
+ eapply Forall_impl; [|exact Xck]. intros k Hk. apply (chunk_ok_cf_app_secs s [sm] k) in Hk.
unfold chunk_ok_cf in *. cbn [st_secs set_chunks set_depot set_sec_arr set_sec_reserved set_secs] in *. exact Hk.
+ constructor; [|constructor]. unfold chunk_ok_cf. cbn [ck_req ck_beg st_secs set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
split; [lia|]. split; [exact Hprim|]. split; [reflexivity|]. exists sm. subst r.
rewrite nth_error_app2, Nat.sub_diag by lia. cbn. repeat split; reflexivity.
- cbn [st_chunks set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite map_app. cbn [map ck_beg].
apply NoDup_app_iff. split; [exact (wfc_chunks_nodup _ _ _ _ _ W)|]. split; [repeat constructor; intros []|].
intros x Hx [<-|[]]. apply in_map_iff in Hx as (k & Hb & Hk). exact (Hfresh k Hk _ Hb).
- cbn [st_chunks st_nev set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite length_app. cbn [length].
pose proof (wfc_chunks_ev _ _ _ _ _ W). lia.
- exact (wfc_prim_ev _ _ _ _ _ W).
- change (blocks_bytes ?[S]) with (blocks_bytes (set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated]) s)).
rewrite blocks_bytes_app1. cbn [is_alloc ck_state ck_req]. lia.
- pose proof (wfc_quarantine _ _ _ _ _ W) as Xq. quar_fields Xq.
constructor; cbn [st_qthread st_qglobal st_chunks set_chunks set_depot set_sec_arr set_sec_reserved set_secs]; try assumption.
eapply Forall_impl; [|exact Qit]. intros k [Hk Hs]. split; [apply in_app_iff; left; exact Hk | exact Hs].
- exact (wfc_batches_ev _ _ _ _ _ W).
- constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
+ apply NoDup_app_iff. split; [exact Snd|]. split; [repeat constructor; intros []|]. intros x Hx [<-|[]]. exact (Hr_notin Hx).
+ intros r'. rewrite in_app_iff. cbn [In]. split.
* intros [Hin|[<-|[]]].
-- apply Sac in Hin as (k & Hk & Hb). exists k. split; [apply in_app_iff; left; exact Hk | exact Hb].
-- eexists. split; [apply in_app_iff; right; left; reflexivity | reflexivity].
* intros (k & Hk & Hb). apply in_app_iff in Hk as [Hk|[<-|[]]].
-- left. apply Sac. exists k. auto.
-- cbn in Hb. injection Hb as <-. right. left. reflexivity.
+ intros r'. rewrite in_app_iff. cbn [In]. split.
* intros [Hin|[<-|[]]].
-- pose proof (proj1 (Sal r') Hin) as (sm' & E & L). exists sm'. rewrite nth_error_app_l by (eapply nth_error_lt; exact E). auto.
-- exists sm. subst r. rewrite nth_error_app2, Nat.sub_diag by lia. split; reflexivity.
* intros (sm' & E & L). destruct (Nat.lt_ge_cases r' (length (st_secs s))) as [Hl|Hl].
-- left. apply (proj2 (Sal r')). exists sm'. rewrite nth_error_app_l in E by exact Hl. auto.
-- right. rewrite nth_error_app2 in E by lia. destruct (r' - length (st_secs s))%nat as [|m] eqn:Em; [left; subst r; lia|].
cbn in E. destruct m; discriminate.
+ rewrite length_app. cbn [length]. pose proof Sral as [S1 S2].
apply Z.mod_divide in S2 as [q Hq]; [|unfold kPtrArrayEntriesPerCommit; lia].
unfold kPtrArrayEntriesPerCommit in *. destruct Hres as [[-> Hlt]|[-> Heq]]; [lia|].
assert (q = 0) by nia. subst q. lia.
+ unfold kPtrArrayEntriesPerCommit in *. destruct Hres as [[-> _]|[-> _]]; [exact Sral|].
destruct Sral as [S1 S2]. split; [lia|]. rewrite Z.add_mod, S2, Z.mod_same by lia. reflexivity.
+ apply Forall_app. split; [exact Slen|]. constructor; [|constructor]. subst sm. cbn [sm_len]. exact (sec_map_size_range_cf n Hn).
- apply (wf_fs_ext s); [reflexivity | exact (wfc_fakestack _ _ _ _ _ W)].
- cbn. exact Hd.
- exact (wfc_nev _ _ _ _ _ W).
- pose proof (wfc_slack _ _ _ _ _ W). lia.
- exact (wfc_qinited _ _ _ _ _ W).
- cbn [st_secs st_nev set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite length_app. cbn [length].
pose proof (wfc_secs_ev _ _ _ _ _ W). lia.
- intros c' Hc'. pose proof (wfc_compl0 _ _ _ _ _ W c' Hc') as HC. unfold cdef in *. rewrite Hce. exact HC.
- cbn [st_sec_arr set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite length_app. cbn [length]. lia.
- apply (qsize_ext s); [reflexivity | reflexivity | exact (wfc_qsize _ _ _ _ _ W)].
Qed.

(* cgif's sec_alloc_ok (YG07.v:227), over atok_cf. Its `1 <= cc` premise is not used and is dropped. *)
Lemma sec_alloc_ok_cf : forall U pp cc bb s n ns,
WfP_cf U pp cc bb s -> 0 <= n < cf_malloc_max -> from_primary n = false ->
atok_cf ns (sec_alloc n s) (sec_alloc_post s n).
Proof.
intros U pp cc bb s n ns W Hn Hprim.
pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ W)) as Sres. pose proof (wsc_reserved_al _ (wfc_secondary _ _ _ _ _ W)) as Sral.
unfold sec_alloc. apply atok_cf_bind. apply atok_cf_askz.
{ cbn [areq_ok_cf]. left. exists n. split; [exact Hn | split; [exact Hprim | reflexivity]]. }
intros z Hz. cbn in Hz. cbn [fst snd progz]. destruct Hz as [-> | ->]; cbn [Z.eqb Pos.eqb].
- apply atok_cf_ret. split; reflexivity.
- apply atok_cf_bind. apply atok_cf_get. cbn [fst snd]. apply atok_cf_bind. apply atok_cf_mcheck.
{ apply Z.ltb_lt. unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia. }
cbn [fst snd]. apply atok_cf_bind. apply atok_cf_put. cbn [fst snd]. apply atok_cf_bind.
destruct (Z.eqb_spec (Z.of_nat (length (st_sec_arr s))) (st_sec_reserved s)) as [Eidx|Nidx].
+ apply atok_cf_bind. apply atok_cf_askz.
{ cbn -[Z.mul Z.add Z.modulo Z.le kPtrArrayCommit kMaxNumChunks]. unfold kPtrArrayCommit, kMaxNumChunks, kPtrArrayEntriesPerCommit in *.
destruct Sral as [S1 S2]. splits; try lia.
all: rewrite Eidx; replace 131072 with (8 * 16384) by reflexivity; rewrite Z.mul_mod_distr_l by lia; rewrite S2; reflexivity. }
intros z2 Hz2. cbn in Hz2. cbn [fst snd]. unfold aGranted. destruct (Z.eqb_spec z2 1) as [->|Nz].
* cbn [progz Z.eqb Pos.eqb]. apply atok_cf_modify. cbn [fst snd]. apply atok_cf_bind. apply atok_cf_modify. cbn [fst snd]. apply atok_cf_ret.
exists (st_sec_reserved s + kPtrArrayEntriesPerCommit). splits; [reflexivity | reflexivity | right; auto | reflexivity].
* replace (progz _ z2) with false. { apply atok_cf_spin. } cbn. destruct Hz2 as [->| ->]; cbn; congruence.
+ apply atok_cf_ret. cbn [fst snd]. apply atok_cf_bind. apply atok_cf_modify. cbn [fst snd]. apply atok_cf_ret.
exists (st_sec_reserved s). splits; [reflexivity | destruct s; reflexivity | left; split; [reflexivity | lia] | reflexivity].
Qed.

(* cgif's prim_chunk_off (YG07.v:175). cgif bounds the offset by 2 ^ 31 = kUserMapSize * EV_MAX; here it is
   bounded by the re-based wrc_mapped_bound, kFreeArrayOffset = 3.5 * 2 ^ 30, still below 2 ^ 32. *)
Lemma prim_chunk_off_cf : forall U pp cc bb s k off, WfP_cf U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim off ->
let c := prim_class off in
1 <= c <= 30 /\ c = chunk_class (ck_req k) /\ from_primary (ck_req k) = true /\ 0 <= ck_req k /\
0 <= off - region_off c < kFreeArrayOffset /\ (off - region_off c) mod class_size c = 0.
Proof.
intros U pp cc bb s k off W Hk Hb c.
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [CKn CK]. rewrite Hb in CK. destruct CK as (CKp & CKc & CKo).
pose proof (primary_geometry (ck_req k) ltac:(lia) CKp) as (Gc & _).
assert (Hc : 1 <= c <= 30) by (subst c; rewrite CKc; exact Gc).
pose proof (In_chunk_offs s k off Hk Hb) as Hin. fold c in Hin.
pose proof (wfc_classes _ _ _ _ _ W c ltac:(lia)) as CL.
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) (off - region_off c)) as E.
specialize (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin)).
pose proof (wrc_alloc _ _ _ _ _ _ CL). assert (Hc31 : 1 <= c <= 31) by lia.
pose proof (mapped_bound_cf U pp cc bb s c W Hc31). subst c. destruct E as [E1 E2].
splits; first [exact CKp | exact CKc | exact E2 | lia].
Qed.

(* cgif's prim_user_inj (YG07.v:191), with the offset window 0 <= x < kFreeArrayOffset. *)
Lemma prim_user_inj_cf : forall U pp cc bb s k boff c x n,
WfP_cf U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim boff ->
1 <= c <= 31 -> 0 <= x < kFreeArrayOffset -> x mod class_size c = 0 -> 0 <= n -> from_primary n = true -> chunk_class n = c ->
boff + ck_rz k = region_off c + x + rz_size n -> boff = region_off c + x.
Proof.
intros U pp cc bb s k boff c x n W Hk Hb Hc Hx Hxa Hn Hp Hcn E.
pose proof (prim_chunk_off_cf U pp cc bb s k boff W Hk Hb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
remember (prim_class boff) as c' eqn:Ec'.
pose proof (rz_size_bounds n) as [[Rn Rn'] _]. pose proof (rz_size_bounds (ck_req k)) as [[Rk Rk'] _]. unfold ck_rz in E.
pose proof (primary_geometry n Hn Hp) as (_ & Sn & _ & _ & Pn). rewrite Hcn in Sn, Pn.
pose proof (primary_geometry (ck_req k) G4 G3) as (_ & Sk & _). rewrite <- G2 in Sk.
pose proof (req_size_bounds n Hn) as (_ & Qn & _). pose proof (req_size_bounds (ck_req k) G4) as (_ & Qk & _).
unfold kFreeArrayOffset in *.
assert (Ec : c' = c).
{ pose proof (prim_class_region_off c' (boff - region_off c' + rz_size (ck_req k)) ltac:(lia) ltac:(lia)) as P1.
pose proof (prim_class_region_off c (x + rz_size n) ltac:(lia) ltac:(lia)) as P2.
replace (region_off c' + (boff - region_off c' + rz_size (ck_req k))) with (region_off c + (x + rz_size n)) in P1 by lia.
congruence. }
subst c'. rewrite Ec in *.
destruct (Z.eq_dec (boff - region_off c) x) as [Eyx|Ne]; [lia|]. exfalso.
assert (D : (boff - region_off c - x) mod class_size c = 0).
{ rewrite Zminus_mod, G6, Hxa. cbn. first [reflexivity | apply Z.mod_0_l; lia]. }
apply Z.mod_divide in D as [q Hq]; [|lia].
assert (Hq0 : q <> 0) by (intros ->; lia).
assert (Habs : class_size c <= Z.abs (boff - region_off c - x)) by nia. lia.
Qed.
End YG07CF.

(* ---------------------------------------------------------------------------- *)
(* malloc_cf.                                                                    *)
Section MALLOC.
Context {cp : CfParams} {ci : CfImg}.

Definition malloc_post_cf (U : Univ) (s : astate) (n : Z) (ns : bool) (r : sptr * astate) : Prop :=
let (p, s') := r in
Wf_cf U s' /\ st_nev s + 1 <= st_nev s' /\ secs_ext_cf s s' /\ frames s' = frames s /\
match p with
| PNull => blocks s' = blocks s
| _ => blocks s' = blocks s ++ [(p, n)] /\ ~ In p (map fst (blocks s))
end /\
(qtight s -> qtight s').

(* kClearShadowMmapThreshold is 2 ^ 64 - 1, so no admissible request asks for the shadow remap. *)
Lemma needs_remap_req_small : forall n, 0 <= n < 2 ^ 30 -> needs_remap (req_size n) = false.
Proof.
intros n Hn. unfold needs_remap, kClearShadowMmapThreshold. apply Z.leb_gt.
pose proof (req_size_bounds n ltac:(lia)) as (_ & _ & Q1 & Q2). lia.
Qed.

Theorem malloc_gen_cf : forall U s n tr,
universe_ok U -> Wf_cf U s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
Z.of_nat (length (st_sec_arr s)) < cf_sec_live_max -> ERRB_ROOM s -> batch_room_cf s ->
atok_cf true (malloc_cf n tr s) (fun ns r => malloc_post_cf U s n ns r /\
(fst r = PNull -> ns = false \/ (from_primary n = true /\ exh_mem_cf (snd r) (chunk_class n) = true))).
Proof.
intros U s n tr HU W Hn Hlive Htr HSEC Hroom H24.
pose proof (WfP_cf_tick' U s W) as W1. set (s1 := set_nev (st_nev s + 1) s) in *.
assert (D1 : depot_fits U (st_depot s1)) by exact (wfc_depot _ _ _ _ _ W1).
pose proof cf_malloc_max_bound as MMB.
assert (NR : needs_remap (req_size n) = false) by (apply needs_remap_req_small; lia).
unfold malloc_cf. apply atok_cf_bind. apply atok_cf_tick. cbn [fst snd]. fold s1.
apply atok_cf_bind. apply atok_cf_mcheck; [apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage in *; lia|]. cbn [fst snd].
apply atok_cf_bind. destruct (from_primary n) eqn:Hprim.
- pose proof (primary_geometry n ltac:(lia) Hprim) as (Gc & Gsz & Gmax & G32 & Gpos).
assert (Hc : 1 <= chunk_class n <= 31) by lia.
assert (H24c : chunk_class n = kBatchClass -> rg_mapped_user (reg s1 (chunk_class n)) + kUserMapSize <= kFreeArrayOffset)
by (intros E; rewrite E; exact H24).
apply atok_cf_bind.
eapply atok_cf_mono; [|apply (cache_alloc_cf_ok U 1 1 1 s1 (chunk_class n) true W1 Hc ltac:(lia) ltac:(lia) H24c Hroom)].
intros ns2 [o s2] (Hi2 & RO2 & Ho). cbn [fst snd] in *. apply atok_cf_ret.
destruct o as [off|].
+ destruct Ho as (s0 & l & W0 & RO0 & Hi0 & El & Hne & -> & ->).
destruct RO0 as (Rck & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev & Rsecs).
assert (Rnev' : st_nev s + 1 <= st_nev s0) by (subst s1; cbn [st_nev set_nev] in Rnev; lia).
assert (HL0 : blocks_bytes s0 + n <= LIVE_MAX) by (unfold blocks_bytes; rewrite Rck; exact Hlive).
cbn [fst snd]. apply atok_cf_bind.
eapply atok_cf_mono; [|apply atok_cf_of_atok; apply (depot_put_ok U _ tr ns2); [ | exact HU | ]].
2:{ unfold upd_pc. cbn [st_depot set_cache fst snd]. rewrite Rdep. exact D1. }
2:{ apply (admits_keep U tr s); [exact Htr|]. left. unfold upd_pc. cbn [st_depot set_cache fst snd]. rewrite Rdep. reflexivity. }
intros ns3 [[] s3] (d & -> & Hdf & Hd & ->). cbn [fst snd]. cbv zeta.
destruct (WfP_cf_pop_add_prim U 0 1 1 s0 (chunk_class n) l n d W0 Hc Hi0 El Hne ltac:(lia) Hn Hprim eq_refl HL0 Hdf)
as (HX1 & HX2 & HX3 & Hfresh & W4).
set (x := last l 0) in *. set (c := chunk_class n) in *.
set (k := mkChunk (PPrim (region_off c + x)) n CAllocated).
replace (needs_remap (ck_n k)) with false by (symmetry; exact NR).
apply atok_cf_bind. apply atok_cf_ret. cbn [fst snd]. apply atok_cf_bind. apply atok_cf_modify. cbn [fst snd]. apply atok_cf_ret.
rewrite upd_chunk_fresh by exact Hfresh.
assert (EB : forall S', st_chunks S' = st_chunks s0 ++ [k] -> blocks S' = blocks s ++ [(PPrim (region_off c + x + rz_size n), n)]).
{ intros S' HS. unfold blocks. rewrite HS, Rck, filter_app, map_app. subst s1 k. reflexivity. }
split; [split; [|split; [|split; [|split; [|split]]]] | ].
* unfold Wf_cf. eapply WfP_cf_weaken; [exact W4 | lia | lia | lia].
* exact Rnev'.
* exact Rsecs.
* unfold frames. unfold upd_pc. cbn [st_fs set_chunks set_depot set_cache]. rewrite Rfs. reflexivity.
* subst k. lazy [ck_user ck_beg ck_rz ck_req padd]. rewrite EB by reflexivity. split; [reflexivity|].
intros Hin. apply in_map_iff in Hin as ([p m] & Hp & Hb). cbn [fst] in Hp. subst p.
apply In_blocks in Hb as (k' & Hk & Hst & Hu & Hr).
unfold ck_user in Hu. destruct (ck_beg k') as [|boff|rr oo|cc' pp'] eqn:Eb; cbn [padd] in Hu; try discriminate.
injection Hu as Hu.
pose proof (prim_user_inj_cf U 0 0 0 s k' boff c x n W Hk Eb Hc ltac:(lia) HX2 ltac:(lia) Hprim eq_refl ltac:(lia)) as J.
apply Hfresh. rewrite Rck. apply in_map_iff. exists k'. split; [rewrite Eb, J; reflexivity | exact Hk].
* apply (qtight_alloc_app s _ k); [unfold upd_pc; cbn [st_chunks set_chunks set_depot set_cache]; rewrite Rck; reflexivity | reflexivity
| unfold upd_pc; cbn [st_qthread set_chunks set_depot set_cache]; rewrite Rqt; reflexivity
| unfold upd_pc; cbn [st_qglobal set_chunks set_depot set_cache]; rewrite Rqg; reflexivity].
* subst k. cbn [fst ck_user ck_beg padd]. intros E. discriminate E.
+ destruct Ho as [W3 NS]. destruct RO2 as (Rck & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev & Rsecs).
apply atok_cf_ret. cbn [fst snd].
split; [split; [|split; [|split; [|split; [|split]]]] | ].
* unfold Wf_cf. eapply WfP_cf_weaken; [exact W3 | lia | lia | lia].
* subst s1. cbn [st_nev set_nev] in Rnev. lia.
* exact Rsecs.
* unfold frames. rewrite Rfs. reflexivity.
* unfold blocks. rewrite Rck. reflexivity.
* apply (qtight_ext s); [rewrite Rck | rewrite Rqt | rewrite Rqg]; reflexivity.
* intros _. destruct NS as [NS|NS]; [left; exact NS | right; split; [reflexivity | exact NS]].
- pose proof (secondary_geometry n ltac:(lia) Hprim) as (S1 & S2 & S3 & S4 & S5 & S6).
eapply atok_cf_mono; [|apply (sec_alloc_ok_cf U 1 1 1 s1 n true W1 Hn Hprim)].
intros ns2 [o s2] Ho. cbn [fst snd] in Ho |- *.
destruct o as [p|].
+ destruct Ho as (res' & -> & -> & Hres & ->).
set (r := length (st_secs s1)). set (sm := mkSec (sec_map_size n) (needed_size n) true).
set (s2 := set_sec_arr _ _).
apply atok_cf_bind. eapply atok_cf_mono; [|apply atok_cf_of_atok; apply (depot_put_ok U s2 tr true); [exact D1 | exact HU | exact (admits_keep U tr s s2 Htr (or_introl eq_refl))]].
intros ns3 [[] s3] (d & -> & Hdf & Hd & ->). cbn [fst snd]. cbv zeta.
set (k := mkChunk (PSec r kPage) n CAllocated).
assert (Hfresh : ~ In (PSec r kPage) (map ck_beg (st_chunks (set_depot d s2)))).
{ cbn [st_chunks set_depot s2 set_sec_arr set_sec_reserved set_secs]. intros Hin. apply in_map_iff in Hin as (k' & Hb & Hk').
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W1) k' Hk') as [_ CK]. rewrite Hb in CK.
destruct CK as (_ & _ & sm' & Es & _). apply nth_error_lt in Es. subst r. lia. }
replace (needs_remap (ck_n k)) with false by (symmetry; exact NR).
apply atok_cf_bind. apply atok_cf_ret. cbn [fst snd]. apply atok_cf_bind. apply atok_cf_modify. cbn [fst snd]. apply atok_cf_ret.
rewrite upd_chunk_fresh by exact Hfresh.
pose proof (WfP_cf_add_sec U 1 1 1 s1 n d res' W1 ltac:(lia) Hn Hprim Hlive Hdf HSEC Hres) as W4.
cbn zeta in W4. fold r sm in W4.
assert (ES : set_chunks (st_chunks (set_depot d s2) ++ [k]) (set_depot d s2)
= set_chunks (st_chunks s1 ++ [k]) (set_depot d (set_sec_arr (st_sec_arr s1 ++ [r]) (set_sec_reserved res' (set_secs (st_secs s1 ++ [sm]) s1))))).
{ subst s2 s1. destruct s. reflexivity. }
rewrite ES.
split; [split; [|split; [|split; [|split; [|split]]]] | ].
* unfold Wf_cf. eapply WfP_cf_weaken; [exact W4 | lia | lia | lia].
* subst s1. cbn. lia.
* apply secs_ext_cf_of_secs_ext. intros r0 sm0 E0. exists sm0. subst s1. cbn.
rewrite nth_error_app1 by (eapply nth_error_lt; exact E0). auto.
* subst s1. reflexivity.
* assert (EB : forall S', st_chunks S' = st_chunks s1 ++ [k] -> blocks S' = blocks s ++ [(PSec r (kPage + rz_size n), n)]).
{ intros S' HS. unfold blocks. rewrite HS, filter_app, map_app. subst s1 k. reflexivity. }
lazy [ck_user ck_beg padd k ck_rz ck_req]. fold k.
rewrite EB by reflexivity. split; [reflexivity|].
intros Hin. apply in_map_iff in Hin as ([p m] & Hp & Hb). cbn [fst] in Hp. subst p.
apply In_blocks in Hb as (k' & Hk' & _ & Hu & _).
unfold ck_user in Hu. destruct (ck_beg k') as [|boff|rr oo|cc' pp'] eqn:Eb; cbn [padd] in Hu; try discriminate.
injection Hu as <- Hoff. apply Hfresh. cbn [st_chunks set_depot s2 set_sec_arr set_sec_reserved set_secs]. subst s1. cbn [st_chunks set_nev].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k' Hk') as [_ CK]. rewrite Eb in CK. destruct CK as (_ & Eoo & _).
apply in_map_iff. exists k'. rewrite Eb, Eoo. auto.
* apply (qtight_alloc_app s _ k); subst s1 k; reflexivity.
* subst k. cbn [fst ck_user ck_beg padd]. intros E. discriminate E.
+ destruct Ho as [-> ->]. apply atok_cf_ret. cbn [fst snd].
split; [split; [|split; [|split; [|split; [|split]]]] | ].
* unfold Wf_cf. eapply WfP_cf_weaken; [exact W1 | lia | lia | lia].
* subst s1. cbn. lia.
* exact (secs_ext_cf_refl s).
* subst s1. reflexivity.
* subst s1. reflexivity.
* apply (qtight_ext s); subst s1; reflexivity.
* intros _. left. reflexivity.
Qed.

(* cgif's malloc_ok (YG07.v:470), the post alone. *)
Theorem malloc_ok_cf : forall U s n tr,
universe_ok U -> Wf_cf U s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
Z.of_nat (length (st_sec_arr s)) < cf_sec_live_max -> ERRB_ROOM s -> batch_room_cf s ->
atok_cf true (malloc_cf n tr s) (malloc_post_cf U s n).
Proof.
intros U s n tr HU W Hn Hlive Htr HSEC Hroom H24.
eapply atok_cf_mono; [|exact (malloc_gen_cf U s n tr HU W Hn Hlive Htr HSEC Hroom H24)]. intros b r (H & _). exact H.
Qed.
End MALLOC.
