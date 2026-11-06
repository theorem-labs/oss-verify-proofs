(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC Q6sh QQwg QvDJ QzgH QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import QCiC.Mq1 QCiC Q6sh QQwg QvDJ QzgH.
Import QCrt.Mq0.
Import ListNotations.
Open Scope Z_scope.

Definition NS {R} (P : R -> Prop) (r : res R) : Prop :=
match r with ROk x => P x | RSpin => False | RUnr _ => True end.

Lemma aokG_grant : forall e a, aokG e a -> exists b, a = AOk b.
Proof. intros e a [_ H]. exact H. Qed.

Lemma tall_bind_NS {R S} (P1 : R -> Prop) (P : S -> Prop) (t : T R) (f : R -> T S) :
tall aokG (NS P1) t -> (forall x, P1 x -> tall aokG (NS P) (f x)) -> tall aokG (NS P) (tbind t f).
Proof.
intros Ht Hf. apply tall_bind. eapply tall_mono; [exact Ht|]. intros [x| |w] H; cbn in *; auto.
Qed.

Lemma tall_rokS {R} (P : R -> Prop) (P' : R -> Prop) (t : T R) :
tall aok0 (rok P) t -> tall aokG (NS P') t -> tall aokG (rokS (fun x => P x /\ P' x)) t.
Proof.
intros H1 H2. pose proof (tall_aok_mono aok0 aokG _ t H1 (fun e a H => proj1 H)) as H1'. clear H1.
induction t as [[x| |w]|e k IH]; cbn in *; auto.
Qed.

Lemma teva_aokG {X} (L : ALay) (BUDGET : Z) (RG : ghost -> X -> Prop) (g : ghost) (t : T X) :
teva L BUDGET aok0 RG g t -> teva L BUDGET aokG RG g t.
Proof.
revert g. induction t as [[x| |w]|e k IH]; intros g H; cbn in *; auto.
destruct H as [Hg Hk]. split; [exact Hg|]. intros a Ha. apply IH. apply Hk. exact (proj1 Ha).
Qed.

Section NoSpin.
Variable L : ALay.

Notation okb := (fun r : bool * AState => fst r = true).

Lemma ensure_fa_ns s c nf : tall aokG (NS okb) (ensure_fa L s c nf).
Proof.
unfold ensure_fa. destruct (_ <=? _); [reflexivity|]. destruct (_ <? _); [exact I|].
intros a Ha. destruct (aokG_grant _ _ Ha) as [b ->]. reflexivity.
Qed.

Lemma populate_ns s c req : tall aokG (NS okb) (populate L s c req).
Proof.
unfold populate. eapply (tall_bind_NS okb).
- destruct (_ <? _); [|reflexivity]. destruct (_ <? _); [exact I|].
intros a Ha. destruct (aokG_grant _ _ Ha) as [b ->]. reflexivity.
- intros [ok s1] H. cbn in H. subst ok. cbn [negb].
eapply (tall_bind_NS okb); [apply ensure_fa_ns|]. intros [ok2 s2] H2. cbn in H2. subst ok2. reflexivity.
Qed.

Lemma get_from_allocator_ns s c k : tall aokG (NS okb) (get_from_allocator L s c k).
Proof.
unfold get_from_allocator. eapply (tall_bind_NS okb).
- destruct (_ <? _); [apply populate_ns| reflexivity].
- intros [ok s1] H. cbn in H. subst ok. cbn [negb]. destruct (_ <? _); [exact I| reflexivity].
Qed.

Lemma refill_ns s c : tall aokG (NS okb) (refill L s c).
Proof.
unfold refill. eapply (tall_bind_NS okb); [apply get_from_allocator_ns|].
intros [ok s1] H. cbn in H. subst ok. reflexivity.
Qed.

Lemma cache_alloc_ns s c : tall aokG (NS okb) (cache_alloc L s c).
Proof.
unfold cache_alloc. eapply (tall_bind_NS okb).
- destruct (_ =? _); [apply refill_ns| reflexivity].
- intros [ok s1] H. cbn in H. subst ok. reflexivity.
Qed.

Notation top := (fun _ => True).

Lemma return_to_allocator_ns s c k : tall aokG (NS top) (return_to_allocator L s c k).
Proof.
unfold return_to_allocator. eapply (tall_bind_NS okb); [apply ensure_fa_ns|].
intros [ok s1] H. cbn in H. subst ok. exact I.
Qed.

Lemma cache_dealloc_ns s c : tall aokG (NS top) (cache_dealloc L s c).
Proof.
unfold cache_dealloc. eapply (tall_bind_NS top).
- destruct (_ =? _); [apply return_to_allocator_ns| exact I].
- intros s1 _. exact I.
Qed.

Lemma clear_shadow_ns a sz : tall aokG (NS top) (clear_shadow a sz).
Proof.
unfold clear_shadow. destruct (remap_range a sz) as [[pb len]|]; [|exact I].
intros x Hx. destruct (aokG_grant _ _ Hx) as [b ->]. exact I.
Qed.

Notation issome := (fun r : option Z * AState => fst r <> None).

Lemma large_alloc_ns s n : tall aokG (NS issome) (large_alloc L s n).
Proof.
unfold large_alloc. intros a Ha. destruct (aokG_grant _ _ Ha) as [mb ->].
destruct (_ <=? _); [exact I|].
eapply (tall_bind_NS top).
- destruct (_ =? _); [|exact I]. intros a2 Ha2. destruct (aokG_grant _ _ Ha2) as [b2 ->]. exact I.
- intros s1 _. cbn. discriminate.
Qed.

Lemma large_dealloc_ns s a : tall aokG (NS top) (large_dealloc s a).
Proof.
unfold large_dealloc. destruct (find_sec a (as_reg s) 0) as [[i e]|]; [|exact I].
eapply (tall_bind_NS top); [apply clear_shadow_ns|]. intros _ _.
intros x Hx. destruct (aokG_grant _ _ Hx) as [b ->]. exact I.
Qed.

Notation gotblock := (fun r : option aptr * AState => fst r <> None).

Lemma asan_malloc_ns s n : tall aokG (NS gotblock) (asan_malloc L s n).
Proof.
unfold asan_malloc. destruct (too_big n); [exact I|]. destruct (from_primary n).
- eapply (tall_bind_NS okb); [apply cache_alloc_ns|]. intros [ok s1] H. cbn in H. subst ok. cbn. discriminate.
- eapply (tall_bind_NS issome); [apply large_alloc_ns|]. intros [r s1] H. cbn in H.
destruct r as [mb|]; [|contradiction].
eapply (tall_bind_NS top); [apply clear_shadow_ns|]. intros _ _. cbn. discriminate.
Qed.

Lemma new_batch_ns s p u : tall aokG (NS top) (new_batch L s p u).
Proof.
unfold new_batch. eapply (tall_bind_NS okb); [apply cache_alloc_ns|].
intros [ok s1] H. cbn in H. subst ok. exact I.
Qed.

Lemma enqueue_ns s p : tall aokG (NS top) (enqueue L s p).
Proof.
unfold enqueue. destruct (split_last _) as [[front b]|]; [|apply new_batch_ns].
destruct (_ =? _); [apply new_batch_ns| exact I].
Qed.

Lemma recycle_chunk_ns s p : tall aokG (NS top) (recycle_chunk L s p).
Proof. destruct p as [i n|a n]; cbn [recycle_chunk]; [apply cache_dealloc_ns| apply large_dealloc_ns]. Qed.

Lemma recycle_chunks_ns ps : forall s, tall aokG (NS top) (recycle_chunks L s ps).
Proof.
induction ps as [|p ps IH]; intros s; cbn [recycle_chunks]; [exact I|].
eapply (tall_bind_NS top); [apply recycle_chunk_ns|]. intros s1 _. apply IH.
Qed.

Lemma do_recycle_ns bs : forall s, tall aokG (NS top) (do_recycle L s bs).
Proof.
induction bs as [|b bs IH]; intros s; cbn [do_recycle]; [exact I|].
eapply (tall_bind_NS top); [apply recycle_chunks_ns|]. intros s1 _.
eapply (tall_bind_NS top); [apply cache_dealloc_ns|]. intros s2 _. apply IH.
Qed.

Lemma recycle_ns s : tall aokG (NS top) (recycle L s).
Proof.
unfold recycle. destruct (_ <? _); [exact I|].
match goal with |- context [if ?b then merge_batches ?g else ?x] => destruct (if b then merge_batches g else x) as [g1 tmp1] end.
destruct (pop_loop _ _ _) as [[g2 tmp]|]; [apply do_recycle_ns| exact I].
Qed.

Lemma drain_ns s : tall aokG (NS top) (drain L s).
Proof. unfold drain. destruct (_ <? _); [apply recycle_ns| exact I]. Qed.

Lemma asan_free_ns s p : tall aokG (NS top) (asan_free L s p).
Proof.
unfold asan_free. eapply (tall_bind_NS top).
- destruct (_ <? _); [apply recycle_chunk_ns| apply enqueue_ns].
- intros s1 _. destruct (_ <? _); [apply drain_ns| exact I].
Qed.

End NoSpin.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi Qcrs QUcd QCUT QwAs Qc6I QJFf QVsB Qsn5 Qqyb Qknc QBrp Q2ui Q1KO Qpj5 QKTr QNqr QeDS QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import Qsn5 QJFf.Mq1 Qqyb.Mq0 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QCiC QvDJ.Mq1.
Import Q6sh QQwg Qpj5.Mq0 QvDJ QKTr QzgH.
Import QNqr QeDS QLiw.Mq1 QCrt.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section ForeignOff.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.

Notation KIx := (KI LV BUDGET PERM TOT0 N0).

Definition fr_in (r : Z * Z) (x : word) : bool := zin (bv_unsigned x) r || zin (bv_unsigned x) (sh_iv LV r).
Definition Fof (FR : list (Z * Z)) (x : word) : bool := existsb (fun r => fr_in r x) FR.

Definition fr_ok (r : Z * Z) : Prop :=
fst r < snd r /\ (snd r <= kLowEnd \/ KHI <= fst r) /\
exists p, In p PERM /\ fst p <= fst r /\ snd r <= snd p /\
zdisj p (al_space_beg L, al_space_beg L + 2^37) /\ zdisj p (al_ptrarr L, al_ptrarr L + 8388608).

Lemma Fof_In : forall FR (x : word), Fof FR x = true -> exists r, In r FR /\
(fst r <= bv_unsigned x < snd r \/ (shz LV (fst r) <= bv_unsigned x < shz LV (snd r - 1) + 1)).
Proof.
intros FR x H. unfold Fof in H. apply existsb_exists in H as (r & Hr & H). exists r. split; [exact Hr|].
unfold fr_in in H. apply orb_prop in H as [H|H]; apply zin_true in H; [left; exact H| right; exact H].
Qed.

Lemma fr_cases : forall r (x : word), fr_ok r ->
(fst r <= bv_unsigned x < snd r \/ (shz LV (fst r) <= bv_unsigned x < shz LV (snd r - 1) + 1)) ->
exists p, In p PERM /\ zdisj p (al_space_beg L, al_space_beg L + 2^37) /\ zdisj p (al_ptrarr L, al_ptrarr L + 8388608) /\
((fst p <= bv_unsigned x < snd p /\ (bv_unsigned x < kLowEnd \/ KHI <= bv_unsigned x))
\/ (kLowEnd <= bv_unsigned x < KHI /\ exists y, fst p <= y < snd p /\ shz LV y = bv_unsigned x)).
Proof.
intros r x (Hne & Hpl & p & Hp & P1 & P2 & D1 & D2) H. exists p. split; [exact Hp|]. split; [exact D1|]. split; [exact D2|].
pose proof (perm_u L LV BUDGET PERM TOT0 N0 LL p Hp) as (_ & _ & _ & R1 & R2 & R3 & Ceil). rewrite Ceil in R3.
destruct H as [H|H].
- left. split; [lia|]. destruct Hpl; [left| right]; lia.
- right. destruct (proj1 (sh_iv_iff LV (fst r) (snd r) (bv_unsigned x) Hne) H) as (y & Hy & Hs).
split; [rewrite <- Hs; apply (shz_in_band L LV BUDGET PERM TOT0 N0 LL); lia|]. exists y. split; [lia| exact Hs].
Qed.

Lemma shz_outside : forall a n y, a mod 8 = 0 -> n mod 8 = 0 -> 0 < n -> (y < a \/ a + n <= y) ->
~ (shz LV a <= shz LV y < shz LV (a + n - 1) + 1).
Proof.
intros a n y Ha Hn Hpos Hy H. destruct (proj1 (sh_iv_iff LV a (a + n) (shz LV y) ltac:(lia)) H) as (y' & Hy' & Hs).
unfold shz in Hs. assert (Hg : y' / 8 = y / 8) by lia. clear - Ha Hn Hy Hy' Hg. Z.div_mod_to_equations. lia.
Qed.

Definition off_app (lo hi : Z) : Prop :=
(hi <= kLowEnd \/ KHI <= lo) /\
forall p, In p PERM -> zdisj p (al_space_beg L, al_space_beg L + 2^37) -> zdisj p (al_ptrarr L, al_ptrarr L + 8388608) ->
zdisj p (lo, hi).
Definition off_sh (lo hi : Z) : Prop :=
exists a n, a mod 8 = 0 /\ n mod 8 = 0 /\ 0 < n /\ 0 <= a /\ a + n <= 2^47 /\
shz LV a <= lo /\ hi <= shz LV (a + n - 1) + 1 /\
forall p, In p PERM -> zdisj p (al_space_beg L, al_space_beg L + 2^37) -> zdisj p (al_ptrarr L, al_ptrarr L + 8388608) ->
zdisj p (a, a + n).

Lemma off_app_F : forall FR lo hi (x : word), Forall fr_ok FR -> off_app lo hi -> Fof FR x = true -> ~ (lo <= bv_unsigned x < hi).
Proof.
intros FR lo hi x HF [Hpl Hd] Hx Hin. apply Fof_In in Hx as (r & Hr & Hx).
destruct (fr_cases r x (proj1 (Forall_forall _ _) HF r Hr) Hx) as (p & Hp & D1 & D2 & [[Hxp _]|[Hb _]]).
- specialize (Hd p Hp D1 D2). unfold zdisj in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

Lemma off_sh_F : forall FR lo hi (x : word), Forall fr_ok FR -> off_sh lo hi -> Fof FR x = true -> ~ (lo <= bv_unsigned x < hi).
Proof.
intros FR lo hi x HF (a & n & Ha & Hn & Hpos & Ha0 & Ha47 & Hlo & Hhi & Hd) Hx Hin. apply Fof_In in Hx as (r & Hr & Hx).
destruct (fr_cases r x (proj1 (Forall_forall _ _) HF r Hr) Hx) as (p & Hp & D1 & D2 & [[Hxp Hnb]|[Hb (y & Hy & Hs)]]).
- assert (Hband : kLowEnd <= bv_unsigned x < KHI).
{ pose proof (shz_in_band L LV BUDGET PERM TOT0 N0 LL a ltac:(lia)) as B1.
pose proof (shz_in_band L LV BUDGET PERM TOT0 N0 LL (a + n - 1) ltac:(lia)) as B2. lia. }
lia.
- specialize (Hd p Hp D1 D2). unfold zdisj in Hd. cbn [fst snd] in Hd.
apply (shz_outside a n y Ha Hn Hpos ltac:(lia)). rewrite Hs. lia.
Qed.

Lemma HSO : shoff_ok LV.
Proof. unfold shoff_ok. rewrite (llo_shoff L LV BUDGET PERM TOT0 N0 LL). unfold kShadowOffset. lia. Qed.

Lemma zeros_cover_one : forall (a n x : word), zeros_cover [(a, n)] x = true <-> bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n.
Proof.
intros a n x. unfold zeros_cover. cbn [existsb fst snd]. rewrite orb_false_r, andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma zeros_cover_cons : forall z zs x, zeros_cover (z :: zs) x = zeros_cover [z] x || zeros_cover zs x.
Proof. intros z zs x. unfold zeros_cover. cbn [existsb]. rewrite orb_false_r. reflexivity. Qed.

Lemma zeros_cover_conceal : forall mo (a n x : word), zeros_cover (conceal LV mo a n) x = true -> In x (bytes_of (shadow_iv LV a n)).
Proof.
intros mo a n x H. unfold zeros_cover in H. apply existsb_exists in H as ([y one] & Hy & H). unfold conceal in Hy.
apply in_map_iff in Hy as (y' & E & Hy'). injection E as <- <-. apply filter_In in Hy' as [Hy' _]. cbn [fst snd] in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
assert (bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
assert (E : x = y') by (apply bv_eq; lia). subst x. exact Hy'.
Qed.

Lemma perm_nonexcl_split : forall r, In r PERM -> excl_entry LV (z2w r) = false -> snd r <= kLowEnd \/ KHI <= fst r.
Proof.
intros r Hr Hex. pose proof (perm_u L LV BUDGET PERM TOT0 N0 LL r Hr) as (U1 & U2 & _ & R1 & R2 & R3 & _).
destruct (Z.le_gt_cases (snd r) kLowEnd) as [H|H]; [left; exact H|].
destruct (Z.le_gt_cases KHI (fst r)) as [H'|H']; [right; exact H'|]. exfalso.
set (y := Z.max (fst r) kLowEnd).
assert (Hy : kLowEnd <= y < KHI) by (unfold y, kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in *; lia).
pose proof (llo_exband L LV BUDGET PERM TOT0 N0 LL y Hy) as HX. apply in_zivs_true in HX as (x & Hx & Hzx).
pose proof (proj1 (excl_entry_false LV (z2w r)) Hex x Hx ltac:(lia) ltac:(rewrite U2; lia)) as D. rewrite U1, U2 in D.
unfold y in *. lia.
Qed.

Theorem ev_rsp_off : forall g mo e rsp mo' evs FR,
KIx g mo -> gev L BUDGET g e -> Forall fr_ok FR ->
nstep_raw LV (node_of e) mo rsp mo' evs -> rsp_off (Fof FR) rsp.
Proof.
intros g mo e rsp mo' evs FR K G HF Hst. destruct e as [len avoid|addr len|pb m|a sz]; cbn [node_of] in Hst.
-
destruct G as (Hlen & Hmod & H40 & _).
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_ANON anon_place_ok grant_model rsp_grant reveal wunit rlenw rlen m_vmmaps] in Hst.
rewrite kind_anon in Hst. destruct Hst as [_ (b & ws & Hpl & Hrev & Hwu & _ & ->)].
unfold anon_place_ok in Hpl. apply andb_prop in Hpl as [Hpl Hfree]. apply andb_prop in Hpl as [Hpl Htop]. apply andb_prop in Hpl as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold kPage in Hmod.
rewrite (rlen_aligned len Hmod) in *. rewrite (rlenw_w64 len Hmod) in *. change (Z_to_bv 64 len) with (w64 len) in Hfree.
pose proof (ki_top_hi LV BUDGET PERM TOT0 N0 g mo K) as HtopC. rewrite kCeil_val in HtopC. unfold kMaxChunk in H40.
assert (Hwl : bv_unsigned (w64 len) = len) by (apply u_w64; lia). unfold page_size in Hal.
pose proof (placement_split L LV BUDGET PERM TOT0 N0 LL g mo b (w64 len) K ltac:(rewrite Hwl; exact Hlen) Hfree) as Hka. rewrite Hwl in Hka.
assert (Hdp : forall p, In p PERM -> zdisj p (bv_unsigned b, bv_unsigned b + len)).
{ intros p Hp. pose proof (ki_perm LV BUDGET PERM TOT0 N0 g mo K p Hp) as (P1 & _).
pose proof (perm_u L LV BUDGET PERM TOT0 N0 LL p Hp) as (U1 & U2 & _).
apply region_free_app in Hfree as [_ Hfm]. rewrite region_free_iff in Hfm.
specialize (Hfm (fst (z2w p)) (snd (z2w p)) ltac:(rewrite <- surjective_pairing; exact P1)). rewrite U1, U2, Hwl in Hfm.
unfold zdisj. cbn [fst snd]. lia. }
pose proof (u_range b) as Hbu.
assert (OA : off_app (bv_unsigned b) (bv_unsigned b + len)) by (split; [exact Hka| intros p Hp _ _; exact (Hdp p Hp)]).
assert (OS : off_sh (shz LV (bv_unsigned b)) (shz LV (bv_unsigned b + len - 1) + 1)).
{ exists (bv_unsigned b), len. split; [clear -Hal; Z.div_mod_to_equations; lia|]. split; [clear -Hmod; Z.div_mod_to_equations; lia|].
split; [exact Hlen|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros p Hp _ _. exact (Hdp p Hp). }
unfold rsp_grant. apply rsp_off_eff.
+ exact Hwu.
+ intros x Fx Hin. rewrite Hrev in Hin. unfold reveal in Hin. apply filter_In in Hin as [Hin _].
apply (bytes_of_shadow LV HSO) in Hin. apply zin_true in Hin. unfold shadow_iv, sh_iv, wiv2z in Hin. cbn [fst snd] in Hin. rewrite Hwl in Hin.
exact (off_sh_F FR _ _ x HF OS Fx Hin).
+ intros x Fx. destruct (zeros_cover [(b, w64 len)] x) eqn:E; [|reflexivity]. exfalso.
apply zeros_cover_one in E. rewrite Hwl in E. exact (off_app_F FR _ _ x HF OA Fx E).
+ intros x _. reflexivity.
-
destruct (ev_fixed_facts L LV BUDGET PERM TOT0 N0 LL g mo addr len K G) as (Hfc & _ & _ & Hadr & Hceil & _).
destruct G as (Hlen & Hmod & Hal & Hwhere & _). unfold kPage in Hmod.
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_FIXED anon_place_ok grant_model rsp_grant reveal wunit rlenw rlen fixed_contained fixed_free commit_model m_vmmaps] in Hst.
rewrite kind_fixed in Hst. change (Z_to_bv 64 addr) with (w64 addr) in Hst. rewrite Hfc in Hst. destruct Hst as [_ [_ ->]].
rewrite (rlenw_w64 len Hmod). rewrite kCeil_val in Hceil.
assert (Hwa : bv_unsigned (w64 addr) = addr) by (apply u_w64; lia).
assert (Hwl : bv_unsigned (w64 len) = len) by (apply u_w64; lia).
assert (OA : off_app addr (addr + len)).
{ destruct Hwhere as [[W1 W2]|[W1 W2]].
- destruct (llo_space L LV BUDGET PERM TOT0 N0 LL) as (r & Hr & Hex & R1 & R2). pose proof (perm_nonexcl_split r Hr Hex) as Hsp.
split; [destruct Hsp; [left| right]; lia|]. intros p _ D _. unfold zdisj in *. cbn [fst snd] in *. lia.
- destruct (llo_parr L LV BUDGET PERM TOT0 N0 LL) as (r & Hr & Hex & R1 & R2). pose proof (perm_nonexcl_split r Hr Hex) as Hsp.
split; [destruct Hsp; [left| right]; lia|]. intros p _ _ D. unfold zdisj in *. cbn [fst snd] in *. lia. }
unfold rsp_grant. apply rsp_off_eff; [reflexivity| intros x _ []| | intros x _; reflexivity].
intros x Fx. destruct (zeros_cover [(w64 addr, w64 len)] x) eqn:E; [|reflexivity]. exfalso.
apply zeros_cover_one in E. rewrite Hwa, Hwl in E. exact (off_app_F FR _ _ x HF OA Fx E).
-
destruct (ev_remap_facts L LV BUDGET PERM TOT0 N0 LL g mo pb m K G) as (_ & _ & Hpb & Hceil & _ & _).
destruct G as (Hm & Hpal & Hmal & (c & Hc & Hlo & Hhi)). unfold kPage in *.
cbn -[mmap_kind QKTr.PROT_RW QKTr.FL_FIXED_NR rsp_remap rlenw rlen remap_model m_vmmaps] in Hst.
rewrite kind_remap in Hst. destruct Hst as [_ [_ ->]]. change (Z_to_bv 64 pb) with (w64 pb).
rewrite (rlenw_w64 m Hmal). rewrite kCeil_val in Hceil.
assert (Hwa : bv_unsigned (w64 pb) = pb) by (apply u_w64; lia).
assert (Hwl : bv_unsigned (w64 m) = m) by (apply u_w64; lia).
pose proof (ki_ch LV BUDGET PERM TOT0 N0 g mo K c Hc) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & _). rewrite kCeil_val in C6.
assert (OS : off_sh pb (pb + m)).
{ exists (fst c), (snd c). split; [clear -C1; Z.div_mod_to_equations; lia|]. split; [clear -C4; Z.div_mod_to_equations; lia|].
split; [exact C2|]. split; [exact C0|]. split; [lia|].
unfold shadow_of in Hlo, Hhi. unfold shz. rewrite (llo_shoff L LV BUDGET PERM TOT0 N0 LL). split; [exact Hlo|]. split; [exact Hhi|].
intros p Hp _ _. pose proof (ki_perm LV BUDGET PERM TOT0 N0 g mo K p Hp) as (_ & _ & _ & _ & P5). exact (P5 c Hc). }
unfold rsp_remap. apply rsp_off_eff; [reflexivity| intros x _ []| | intros x _; reflexivity].
intros x Fx. destruct (zeros_cover [(w64 pb, w64 m)] x) eqn:E; [|reflexivity]. exfalso.
apply zeros_cover_one in E. rewrite Hwa, Hwl in E. exact (off_sh_F FR _ _ x HF OS Fx E).
-
destruct G as [Hc Hsz].
pose proof (ki_ch LV BUDGET PERM TOT0 N0 g mo K _ Hc) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & _). cbn [fst snd] in *. rewrite kCeil_val in C6.
cbn -[rsp_munmap rlenw rlen munmap_model m_vmmaps] in Hst. destruct Hst as (_ & _ & ->).
change (Z_to_bv 64 a) with (w64 a). rewrite (rlenw_w64 sz C4).
assert (Hwa : bv_unsigned (w64 a) = a) by (apply u_w64; lia).
assert (Hwl : bv_unsigned (w64 sz) = sz) by (apply u_w64; lia).
assert (Hdp : forall p, In p PERM -> zdisj p (a, a + sz)).
{ intros p Hp. pose proof (ki_perm LV BUDGET PERM TOT0 N0 g mo K p Hp) as (_ & _ & _ & _ & P5). exact (P5 _ Hc). }
assert (OA : off_app a (a + sz)) by (split; [exact C5| intros p Hp _ _; exact (Hdp p Hp)]).
assert (OS : off_sh (shz LV a) (shz LV (a + sz - 1) + 1)).
{ exists a, sz. split; [clear -C1; Z.div_mod_to_equations; lia|]. split; [clear -C4; Z.div_mod_to_equations; lia|].
split; [exact C2|]. split; [exact C0|]. split; [lia|]. split; [lia|]. split; [lia|]. intros p Hp _ _. exact (Hdp p Hp). }
unfold rsp_munmap. apply rsp_off_eff; [reflexivity| intros x _ []| intros x _; reflexivity|].
intros x Fx. rewrite zeros_cover_cons. apply orb_false_intro.
+ destruct (zeros_cover [(w64 a, w64 sz)] x) eqn:E; [|reflexivity]. exfalso.
apply zeros_cover_one in E. rewrite Hwa, Hwl in E. exact (off_app_F FR _ _ x HF OA Fx E).
+ destruct (zeros_cover (conceal LV mo' (w64 a) (w64 sz)) x) eqn:E; [|reflexivity]. exfalso.
apply zeros_cover_conceal in E. apply (bytes_of_shadow LV HSO) in E. apply zin_true in E.
unfold shadow_iv, sh_iv, wiv2z in E. cbn [fst snd] in E. rewrite Hwa, Hwl in E.
exact (off_sh_F FR _ _ x HF OS Fx E).
Qed.

End ForeignOff.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QCiC QvDJ.Mq1.
Import Q6sh QQwg Qpj5.Mq0 QvDJ QKTr QzgH.
Import QNqr QeDS QNqr.Mq0 QCrt.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section LedgerNodes.
Variable segs : list Segment.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Notation KIx := (KI LV BUDGET PERM TOT0 N0).

Variable J : config -> Prop.
Hypothesis J_nclosed : forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, J (nx i)) -> J c.

Theorem vj_ev : forall (e : evA) (g : ghost) c msv,
at_nodeA LV segs (node_of e) msv ->
cinvA LV (cfg_ms c) (cfg_model c) ->
KIx g (cfg_model c) -> gev L BUDGET g e ->
(forall rsp ans c1 mo1,
drift LV (cfg_model c) mo1 -> nstep_raw LV (node_of e) mo1 rsp (cfg_model c1) [] ->
dec_of e rsp = Some ans -> aok0 e ans -> KIx (gstep g e ans) (cfg_model c1) ->
cinvA LV (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
VJ LV J c1 (nret msv rsp)) ->
VJ LV J c msv.
Proof.
intros e g c msv Hat HC K G HK.
apply (vj_silent node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) (nodesA_sound segs LV Hsegs Hsh Hbx Hbc) J J_nclosed (node_of e) c msv Hat HC).
- apply node_of_not_spin.
- exact (ev_safe L LV BUDGET PERM TOT0 N0 LL g _ e K G).
- intros mo1 code mo' _. apply node_of_no_exit.
- intros rsp mo' evs (mo1 & _ & Hr). exact (node_of_silent LV e mo1 rsp mo' evs Hr).
- intros rsp c1 (mo1 & Hd & Hr) HC1 Hh1.
pose proof (KI_drift LV BUDGET PERM TOT0 N0 g _ _ Hd K) as K1.
destruct (ev_step L LV BUDGET PERM TOT0 N0 LL g mo1 e rsp _ [] K1 G Hr) as (ans & Hdec & Hok & K').
exact (HK rsp ans c1 mo1 Hd Hr Hdec Hok K' HC1 Hh1).
Qed.

End LedgerNodes.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH QdZp QTtp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QNqr QNqr.Mq0 QeDS.Mq1 QTtp QLiw.Mq3 QCrt.Mq3.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Section Stderr.
Context {St : Type}.

Lemma mio_stderr_fwrite : forall s, mio (stderr_fwrite (St:=St) s).
Proof. intros s. unfold stderr_fwrite. apply mio_if; [apply mio_stdio_writev| apply mio_ret]. Qed.

Lemma mdet_stderr_fwrite : forall s (st : St), zlength s < 2^64 -> mdet (stderr_fwrite s) st (wev 2 s) tt st.
Proof.
intros s st H. unfold stderr_fwrite. destruct (0 <? zlength s) eqn:E.
- apply (mdet_stdio_writev 2 [] s st). unfold zlength in *. cbn [length]. lia.
- apply Z.ltb_ge in E. assert (s = []) by (destruct s; [reflexivity| unfold zlength in E; cbn in E; lia]). subst s.
apply mdet_ret.
Qed.

Fixpoint sp_run (buf : list Z) (ps : list (list Z)) : list Z * list Z :=
match ps with
| [] => ([], buf)
| p :: ps' =>
if INTERNAL_BUFSIZ - zlength buf <? zlength p
then let r := sp_run [] ps' in (buf ++ p ++ fst r, snd r)
else sp_run (buf ++ p) ps'
end.

Lemma sp_run_total : forall ps buf, fst (sp_run buf ps) ++ snd (sp_run buf ps) = buf ++ concat ps.
Proof.
induction ps as [|p ps IH]; intros buf; cbn [sp_run concat].
- rewrite app_nil_r. reflexivity.
- destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); cbn [fst snd].
+ rewrite <- !app_assoc. rewrite (IH []). reflexivity.
+ rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Lemma mio_stderr_pieces : forall ps buf, mio (stderr_pieces (St:=St) buf ps).
Proof.
induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply mio_ret|].
apply mio_if; [|apply IH]. apply mio_bind; [apply mio_stdio_writev| intros; apply IH].
Qed.

Lemma mdet_stderr_pieces : forall ps buf (st : St), zlength buf + zlength (concat ps) < 2^64 ->
mdet (stderr_pieces buf ps) st (wev 2 (fst (sp_run buf ps))) (snd (sp_run buf ps)) st.
Proof.
induction ps as [|p ps IH]; intros buf st H; cbn [stderr_pieces sp_run].
- cbn [fst snd]. apply mdet_ret.
- cbn [concat] in H. unfold zlength in H. rewrite length_app in H.
destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); cbn [fst snd].
+ eapply mdet_out_eq; [|eapply mdet_bind; [apply (mdet_stdio_writev 2 buf p st); unfold zlength; lia|]].
2:{ apply (IH [] st). unfold zlength. cbn [length]. lia. }
rewrite <- wev_app. rewrite <- app_assoc. reflexivity.
+ apply IH. unfold zlength. rewrite length_app. lia.
Qed.

Lemma mio_stderr_fprintf : forall ps, mio (stderr_fprintf (St:=St) ps).
Proof. intros ps. unfold stderr_fprintf. apply mio_bind; [apply mio_stderr_pieces| intros; apply mio_stdio_writev]. Qed.

Theorem mdet_stderr_fprintf : forall ps (st : St), zlength (concat ps) < 2^64 ->
mdet (stderr_fprintf ps) st (wev 2 (concat ps)) tt st.
Proof.
intros ps st H. unfold stderr_fprintf.
pose proof (sp_run_total ps []) as T. cbn [app] in T.
eapply mdet_out_eq; [|eapply mdet_bind; [apply (mdet_stderr_pieces ps [] st); unfold zlength in *; cbn [length]; lia|]].
2:{ apply (mdet_stdio_writev 2 (snd (sp_run [] ps)) [] st).
assert (L : zlength (snd (sp_run [] ps)) <= zlength (concat ps)) by (rewrite <- T; unfold zlength; rewrite length_app; lia).
unfold zlength in *. cbn [length]. lia. }
rewrite app_nil_r. rewrite <- wev_app. rewrite T. reflexivity.
Qed.

End Stderr.

Section Stdout.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall x so, get_so (set_so so x) = so.
Hypothesis set_set : forall x so so', set_so so' (set_so so x) = set_so so' x.
Local Notation M := (Qpj5.Mq1.M St).

Definition same_off (st st' : St) : Prop := forall x, set_so x st' = set_so x st.
Definition sdet {A} (c : M A) (st : St) (out : list event) (a : A) (so' : stdout_st) : Prop :=
exists st', mdet c st out a st' /\ get_so st' = so' /\ same_off st st'.

Lemma same_off_refl : forall st, same_off st st. Proof. intros st x. reflexivity. Qed.
Lemma same_off_set : forall st st' so, same_off st st' -> same_off st (set_so so st').
Proof. intros st st' so H x. rewrite set_set. apply H. Qed.

Lemma sdet_ret : forall {A} (a : A) st so, get_so st = so -> sdet (mret a) st [] a so.
Proof. intros A a st so G. exists st. split; [apply mdet_ret|]. split; [exact G| apply same_off_refl]. Qed.

Lemma sdet_bind : forall {A B} (m : M A) (f : A -> M B) st o1 a so1 o2 b so2,
sdet m st o1 a so1 ->
(forall st1, get_so st1 = so1 -> sdet (f a) st1 o2 b so2) ->
sdet (mbind m f) st (o1 ++ o2) b so2.
Proof.
intros A B m f st o1 a so1 o2 b so2 (st1 & D1 & G1 & S1) Hf.
destruct (Hf st1 G1) as (st2 & D2 & G2 & S2).
exists st2. split; [exact (mdet_bind m f st o1 a st1 o2 b st2 D1 D2)|]. split; [exact G2|].
intros x. rewrite S2. apply S1.
Qed.

Lemma sdet_out_eq : forall {A} (c : M A) st out out' a so', out = out' -> sdet c st out a so' -> sdet c st out' a so'.
Proof. intros; subst; assumption. Qed.

Lemma sdet_so_eq : forall {A} (c : M A) st out a so' so'', so' = so'' -> sdet c st out a so' -> sdet c st out a so''.
Proof. intros; subst; assumption. Qed.

Lemma sdet_of_mdet : forall {A} (c : M A) st so out a, get_so st = so -> mdet c st out a st -> sdet c st out a so.
Proof. intros A c st so out a G D. exists st. split; [exact D|]. split; [exact G| apply same_off_refl]. Qed.

Lemma sdet_rd_so : forall st so, get_so st = so -> sdet (rd_so get_so) st [] so so.
Proof.
intros st so G. apply sdet_of_mdet; [exact G|]. rewrite <- G.
unfold rd_so. apply (mdet_bind mget (fun s => mret (get_so s)) st [] st st [] (get_so st) st); [apply mdet_get| apply mdet_ret].
Qed.

Lemma sdet_upd_so : forall f st so, get_so st = so -> sdet (upd_so get_so set_so f) st [] tt (f so).
Proof.
intros f st so G. exists (set_so (f (get_so st)) st). split; [exact (mdet_upd (fun s => set_so (f (get_so s)) s) st)|].
split; [rewrite get_set, G; reflexivity|]. apply same_off_set, same_off_refl.
Qed.

Ltac s_upd G := lazymatch goal with |- sdet (upd_so _ _ ?f) ?st _ _ _ => apply (sdet_upd_so f st _ G) end.

Definition so_stdio_write (so : stdout_st) (s : list Z) : list Z * stdout_st :=
(so_buf so ++ s, mkStdout true [] (so_lbf_nl so) (so_first so)).
Definition so_writefn (so : stdout_st) (s : list Z) : list Z * stdout_st :=
so_stdio_write (if so_first so then mkStdout (so_active so) (so_buf so) false false else so) s.
Definition so_towrite (so : stdout_st) : stdout_st :=
if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so).
Definition so_fwritex (so0 : stdout_st) (s : list Z) : list Z * stdout_st :=
let so := so_towrite so0 in
if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s then so_writefn so s
else if so_lbf_nl so then
let i := after_last_nl s in
let r := if 0 <? i then so_writefn so (firstn (Z.to_nat i) s) else ([], so) in
(fst r, mkStdout (so_active (snd r)) (so_buf (snd r) ++ skipn (Z.to_nat i) s) (so_lbf_nl (snd r)) (so_first (snd r)))
else ([], mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).
Fixpoint so_pieces (so : stdout_st) (ps : list (list Z)) : list Z * stdout_st :=
match ps with
| [] => ([], so)
| p :: ps' => let r := so_fwritex so p in let r' := so_pieces (snd r) ps' in (fst r ++ fst r', snd r')
end.
Definition so_vprintf (so : stdout_st) (ps : list (list Z)) : list Z * stdout_st := so_pieces (so_towrite so) ps.
Definition so_exit_flush (so : stdout_st) : list Z * stdout_st :=
if 0 <? zlength (so_buf so) then so_writefn so [] else ([], so).

Lemma sdet_stdout_stdio_write : forall s st so, get_so st = so -> zlength (so_buf so) + zlength s < 2^64 ->
sdet (stdout_stdio_write get_so set_so s) st (wev 1 (fst (so_stdio_write so s))) tt (snd (so_stdio_write so s)).
Proof.
intros s st so G H. unfold stdout_stdio_write, so_stdio_write. cbn [fst snd].
eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_rd_so st so G)|]].
2:{ intros st1 G1. eapply sdet_bind.
- apply (sdet_of_mdet _ st1 so _ _ G1). apply mdet_stdio_writev. exact H.
- intros st2 G2. s_upd G2. }
cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma sdet_stdout_writefn : forall s st so, get_so st = so -> zlength (so_buf so) + zlength s < 2^64 ->
sdet (stdout_writefn get_so set_so s) st (wev 1 (fst (so_writefn so s))) tt (snd (so_writefn so s)).
Proof.
intros s st so G H. unfold stdout_writefn, so_writefn. destruct (so_first so) eqn:F.
- eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_rd_so st so G)|]].
2:{ intros st1 G1. rewrite F. eapply sdet_bind.
- eapply sdet_bind; [s_upd G1|]. intros st2 G2.
eapply sdet_bind; [apply (sdet_of_mdet _ st2 _ _ _ G2); apply mdet_ioctl|]. intros st3 G3. cbv iota.
s_upd G3.
- intros st4 G4. apply (sdet_stdout_stdio_write s st4 _ G4). cbn [so_buf]. exact H. }
cbn [app so_active so_buf so_lbf_nl so_first]. reflexivity.
- eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_rd_so st so G)|]].
2:{ intros st1 G1. rewrite F. eapply sdet_bind; [apply (sdet_ret tt st1 so G1)|].
intros st4 G4. apply (sdet_stdout_stdio_write s st4 _ G4). exact H. }
reflexivity.
Qed.

Lemma so_writefn_buf : forall so s, so_buf (snd (so_writefn so s)) = [].
Proof. intros so s. unfold so_writefn, so_stdio_write. reflexivity. Qed.

Lemma sdet_stdout_towrite : forall st so, get_so st = so -> sdet (stdout_towrite get_so set_so) st [] tt (so_towrite so).
Proof. intros st so G. unfold stdout_towrite, so_towrite. s_upd G. Qed.

Lemma so_towrite_buf : forall so, zlength (so_buf so) <= STDOUT_BUFSIZ -> zlength (so_buf (so_towrite so)) <= STDOUT_BUFSIZ.
Proof. intros so H. unfold so_towrite. destruct (so_active so); [exact H| cbn [so_buf]; unfold zlength, STDOUT_BUFSIZ; cbn [length]; lia]. Qed.

Lemma sdet_stdout_fwritex : forall s st so, get_so st = so ->
zlength (so_buf so) <= STDOUT_BUFSIZ -> zlength s < 2^63 ->
sdet (stdout_fwritex get_so set_so s) st (wev 1 (fst (so_fwritex so s))) tt (snd (so_fwritex so s)).
Proof.
intros s st so G HB HS. unfold stdout_fwritex, so_fwritex.
pose proof (so_towrite_buf so HB) as HB'. set (so1 := so_towrite so) in *.
assert (HF : zlength (firstn (Z.to_nat (after_last_nl s)) s) <= zlength s) by (unfold zlength; rewrite length_firstn; lia).
destruct (STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s) eqn:E1; [|destruct (so_lbf_nl so1) eqn:E2; [destruct (0 <? after_last_nl s) eqn:E3|]].
- eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_stdout_towrite st so G)|]].
2:{ intros st1 G1. fold so1 in G1. eapply sdet_bind; [apply (sdet_rd_so st1 so1 G1)|]. intros st2 G2. rewrite E1.
apply (sdet_stdout_writefn s st2 so1 G2). unfold STDOUT_BUFSIZ in *. lia. }
reflexivity.
- eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_stdout_towrite st so G)|]].
2:{ intros st1 G1. fold so1 in G1. eapply sdet_bind; [apply (sdet_rd_so st1 so1 G1)|]. intros st2 G2. rewrite E1, E2. cbv zeta.
eapply sdet_bind; [apply (sdet_stdout_writefn _ st2 so1 G2); unfold STDOUT_BUFSIZ in *; lia|].
intros st3 G3. s_upd G3. }
cbn [app fst snd]. rewrite app_nil_r. reflexivity.
- eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_stdout_towrite st so G)|]].
2:{ intros st1 G1. fold so1 in G1. eapply sdet_bind; [apply (sdet_rd_so st1 so1 G1)|]. intros st2 G2. rewrite E1, E2. cbv zeta.
eapply sdet_bind; [apply (sdet_ret tt st2 so1 G2)|].
intros st3 G3. s_upd G3. }
reflexivity.
- eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_stdout_towrite st so G)|]].
2:{ intros st1 G1. fold so1 in G1. eapply sdet_bind; [apply (sdet_rd_so st1 so1 G1)|]. intros st2 G2. rewrite E1, E2.
eapply sdet_so_eq; [|s_upd G2]. cbn [snd]. rewrite E2. reflexivity. }
reflexivity.
Qed.

Lemma so_fwritex_buf : forall so s, zlength (so_buf so) <= STDOUT_BUFSIZ ->
zlength (so_buf (snd (so_fwritex so s))) <= STDOUT_BUFSIZ.
Proof.
intros so s HB. unfold so_fwritex. pose proof (so_towrite_buf so HB) as HB'. set (so1 := so_towrite so) in *.
assert (HK : zlength (skipn (Z.to_nat (after_last_nl s)) s) <= zlength s) by (unfold zlength; rewrite length_skipn; lia).
destruct (STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s) eqn:E1.
- rewrite so_writefn_buf. unfold zlength, STDOUT_BUFSIZ. cbn [length]. lia.
- apply Z.ltb_ge in E1. destruct (so_lbf_nl so1).
+ cbn [snd so_buf]. destruct (0 <? after_last_nl s); cbn [snd].
* rewrite so_writefn_buf. cbn [app]. unfold STDOUT_BUFSIZ in *. pose proof (Zle_0_nat (length (so_buf so1))). unfold zlength in *. lia.
* unfold zlength in *. rewrite length_app. lia.
+ cbn [snd so_buf]. unfold zlength in *. rewrite length_app. lia.
Qed.

Lemma sdet_out_pieces : forall ps st so, get_so st = so ->
zlength (so_buf so) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p < 2^63) ps ->
sdet (out_pieces get_so set_so ps) st (wev 1 (fst (so_pieces so ps))) tt (snd (so_pieces so ps)).
Proof.
induction ps as [|p ps IH]; intros st so G HB HP; cbn [out_pieces so_pieces].
- cbn [fst snd]. apply (sdet_ret tt st so G).
- apply Forall_cons_iff in HP. destruct HP as [Hp HP']. cbn [fst snd].
eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_stdout_fwritex p st so G HB Hp)|]].
2:{ intros st1 G1. apply (IH st1 _ G1 (so_fwritex_buf so p HB) HP'). }
rewrite <- wev_app. reflexivity.
Qed.

Theorem sdet_stdout_vprintf : forall ps st so, get_so st = so ->
zlength (so_buf so) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p < 2^63) ps ->
sdet (stdout_vprintf get_so set_so ps) st (wev 1 (fst (so_vprintf so ps))) tt (snd (so_vprintf so ps)).
Proof.
intros ps st so G HB HP. unfold stdout_vprintf, so_vprintf.
eapply sdet_out_eq; [|eapply sdet_bind; [apply (sdet_stdout_towrite st so G)|]].
2:{ intros st1 G1. apply (sdet_out_pieces ps st1 _ G1 (so_towrite_buf so HB) HP). }
reflexivity.
Qed.

Lemma mio_rd_so : mio (rd_so get_so).
Proof. unfold rd_so. apply mio_bind; [apply mio_get| intros; apply mio_ret]. Qed.
Lemma mio_upd_so : forall f, mio (upd_so get_so set_so f).
Proof. intros f. unfold upd_so. apply mio_upd. Qed.
Lemma mio_stdout_stdio_write : forall s, mio (stdout_stdio_write get_so set_so s).
Proof.
intros s. unfold stdout_stdio_write. apply mio_bind; [apply mio_rd_so|]. intros so.
apply mio_bind; [apply mio_stdio_writev| intros; apply mio_upd_so].
Qed.
Lemma mio_stdout_writefn : forall s, mio (stdout_writefn get_so set_so s).
Proof.
intros s. unfold stdout_writefn. apply mio_bind; [apply mio_rd_so|]. intros so.
apply mio_bind; [|intros; apply mio_stdout_stdio_write].
apply mio_if; [|apply mio_ret]. apply mio_bind; [apply mio_upd_so|]. intros _.
apply mio_bind; [apply mio_sys; exact I|]. intros [e|v]; [apply mio_upd_so| apply mio_unr].
Qed.
Lemma mio_stdout_fwritex : forall s, mio (stdout_fwritex get_so set_so s).
Proof.
intros s. unfold stdout_fwritex, stdout_towrite. apply mio_bind; [apply mio_upd_so|]. intros _.
apply mio_bind; [apply mio_rd_so|]. intros so.
apply mio_if; [apply mio_stdout_writefn|]. apply mio_if; [|apply mio_upd_so]. cbv zeta.
apply mio_bind; [apply mio_if; [apply mio_stdout_writefn| apply mio_ret]| intros; apply mio_upd_so].
Qed.
Lemma mio_out_pieces : forall ps, mio (out_pieces get_so set_so ps).
Proof. induction ps as [|p ps IH]; cbn [out_pieces]; [apply mio_ret|]. apply mio_bind; [apply mio_stdout_fwritex| intros; apply IH]. Qed.
Lemma mio_stdout_vprintf : forall ps, mio (stdout_vprintf get_so set_so ps).
Proof. intros ps. unfold stdout_vprintf, stdout_towrite. apply mio_bind; [apply mio_upd_so| intros; apply mio_out_pieces]. Qed.

End Stdout.

Section RuleS.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Theorem implM_vj_sdet : forall {St A} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St)
(c : Qpj5.Mq1.M St A) (s : St) (Q : A -> St -> machine_state -> Prop)
(out : list event) (a : A) (so' : stdout_st) (K : TSet) c0 msv,
Qpj5.Mq1.implM segs c s Q msv ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
mio c -> sdet get_so set_so c s out a so' -> K [] ->
(forall st' c1 msv1, get_so st' = so' ->
evt segs (Q a st') msv1 -> drift LV (cfg_model c0) (cfg_model c1) ->
cinvA LV (cfg_ms c1) (cfg_model c1) ->
msview LV (cfg_model c1) (cfg_ms c1) = msv1 \/ (c1 = c0 /\ msv1 = msv) ->
VJ LV (JS segs K) c1 msv1) ->
VJ LV (JS segs (t_emit out K)) c0 msv.
Proof.
intros St A get_so set_so c s Q out a so' K c0 msv Himpl HC Hio (st' & D & G & _) HK0 HK.
apply (implM_vj_det segs LV Hwx Hsegs Hsh Hbx Hbc c s Q out a st' K c0 msv Himpl HC (Hio s) D HK0).
intros c1 msv1. apply (HK st' c1 msv1 G).
Qed.
End RuleS.

Example so_vprintf_emit0_first : so_vprintf stdout_init (pieces_emit_d 0) = ([48; 10], mkStdout true [] false false).
Proof. vm_compute. reflexivity. Qed.
Lemma pieces_emit_d_0 : pieces_emit_d 0 = [ ([] : list Z); []; [48]; []; [10] ].
Proof. vm_compute. reflexivity. Qed.

Lemma so_fwritex_append : forall b s, zlength b + zlength s <= STDOUT_BUFSIZ ->
so_fwritex (mkStdout true b false false) s = ([], mkStdout true (b ++ s) false false).
Proof.
intros b s Hb. unfold so_fwritex, so_towrite. cbn [so_active so_buf so_lbf_nl so_first].
replace (STDOUT_BUFSIZ - zlength b <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma so_pieces_append_step : forall b p ps, zlength b + zlength p <= STDOUT_BUFSIZ ->
so_pieces (mkStdout true b false false) (p :: ps) = so_pieces (mkStdout true (b ++ p) false false) ps.
Proof.
intros b p ps H.
assert (S1 : forall so q qs, so_pieces so (q :: qs) = (fst (so_fwritex so q) ++ fst (so_pieces (snd (so_fwritex so q)) qs), snd (so_pieces (snd (so_fwritex so q)) qs))) by reflexivity.
rewrite S1, (so_fwritex_append b p H). cbn [fst snd app].
destruct (so_pieces (mkStdout true (b ++ p) false false) ps). reflexivity.
Qed.

Lemma so_vprintf_emit0_next : forall buf, zlength buf + 2 <= STDOUT_BUFSIZ ->
so_vprintf (mkStdout true buf false false) (pieces_emit_d 0) = ([], mkStdout true (buf ++ [48; 10]) false false).
Proof.
intros buf H. rewrite pieces_emit_d_0. unfold so_vprintf, so_towrite. cbn [so_active].
assert (L0 : zlength (@nil Z) = 0) by reflexivity. assert (L1 : forall x : Z, zlength [x] = 1) by reflexivity.
assert (LA : forall (x : list Z) y, zlength (x ++ y) = zlength x + zlength y) by (intros; unfold zlength; rewrite length_app; lia).
rewrite (so_pieces_append_step buf []) by (rewrite L0; lia). rewrite app_nil_r.
rewrite (so_pieces_append_step buf []) by (rewrite L0; lia). rewrite app_nil_r.
rewrite (so_pieces_append_step buf [48]) by (rewrite L1; lia).
rewrite (so_pieces_append_step (buf ++ [48]) []) by (rewrite LA, L1, L0; lia). rewrite (app_nil_r (buf ++ [48])).
rewrite (so_pieces_append_step (buf ++ [48]) [10]) by (rewrite LA, !L1; lia).
rewrite <- app_assoc. reflexivity.
Qed.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvsx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvsx.Mq0.
Import ListNotations.
Open Scope Z_scope.

Definition kCapN : Z := 15900.

Definition cap_class_check (n : Z) : bool := let c := class_of n in class_size c * (kCapN + 17) + qcap c <=? kFreeArrayOffset.
Lemma cap_class_tab : forall_range cap_class_check 0 64513 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zcount_le_zlen : forall {A} (f : A -> bool) l, zcount f l <= zlen l.
Proof.
intros A f l. unfold zcount, zlen. induction l as [|x l IH]; cbn [List.filter length]; [lia|]. destruct (f x); cbn [length]; lia.
Qed.

Lemma secs_le_zlen : forall X, zlen (secs X) <= zlen X.
Proof.
induction X as [|x X IH]; [apply Z.le_refl|]. pose proof (secs_cons_le x X). rewrite (zlen_cons x X). lia.
Qed.

Theorem cap_ok_of_len : forall X, zlen X <= kCapN -> cap_ok X.
Proof.
intros X HX. split.
- intros n Hn Hp. pose proof (forall_range_spec class_of_check 0 64513 64513 class_of_tab eq_refl n) as Hc.
pose proof (from_primary_le n Hn Hp) as Hle. specialize (Hc ltac:(lia)). unfold class_of_check in Hc.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [C1 C2].
apply Z.leb_le in C1, C2.
pose proof (forall_range_spec cap_class_check 0 64513 64513 cap_class_tab eq_refl n ltac:(lia)) as Hk.
unfold cap_class_check in Hk. cbv zeta in Hk. apply Z.leb_le in Hk.
pose proof (zcount_le_zlen (is_cls (class_of n)) X) as Hcnt. fold (cntc (class_of n) X) in Hcnt.
assert (Hsz : 0 <= class_size (class_of n)).
{ pose proof (class_facts (class_of n) ltac:(lia)) as (Hs & _). lia. }
nia.
- pose proof (secs_le_zlen X). unfold kMaxSecs, kCapN in *. lia.
Qed.

Lemma mcost_le_acost : forall n, 0 <= n <= 2^26 -> mcost n <= (if n <=? 64512 then 0 else 3 * n + 45101).
Proof.
intros n Hn. unfold mcost. destruct (Z.leb_spec n 64512) as [Hs|Hs].
- assert (Hp : from_primary n = true).
{ unfold from_primary, needed, rz_size, kMaxSize, round_up.
assert (H8 : (Z.max n 8 + 8 - 1) / 8 * 8 <= Z.max n 8 + 7) by (pose proof (Z.mul_div_le (Z.max n 8 + 8 - 1) 8 ltac:(lia)); lia).
apply Z.leb_le.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); [|lia].

assert ((Z.max n 8 + 8 - 1) / 8 < 8065) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite Hp. lia.
- destruct (from_primary n) eqn:Hp; [pose proof (from_primary_le n ltac:(lia) Hp); lia|].
unfold sec_cost, sec_map_size, needed, rz_size, round_up, kPage.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); [lia|].
assert (H8 : (Z.max n 8 + 8 - 1) / 8 * 8 <= n + 7) by (pose proof (Z.mul_div_le (Z.max n 8 + 8 - 1) 8 ltac:(lia)); lia).
set (nd := (Z.max n 8 + 8 - 1) / 8 * 8 + 2048) in *.
assert (Hnd : 0 <= nd <= n + 2055) by (unfold nd; pose proof (Z.div_pos (Z.max n 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)); lia).
assert (Hm : (nd + 2048 + 4096 - 1) / 4096 * 4096 <= nd + 2048 + 4095) by (pose proof (Z.mul_div_le (nd + 2048 + 4096 - 1) 4096 ltac:(lia)); lia).
set (len := (nd + 2048 + 4096 - 1) / 4096 * 4096 + 4096) in *.
assert (Hlen : 0 <= len <= n + 12294) by (unfold len; pose proof (Z.div_pos (nd + 2048 + 4096 - 1) 4096 ltac:(lia) ltac:(lia)); lia).
assert (Hd : len / 32768 <= len / 8 / 4096) by (rewrite Z.div_div by lia; change (8 * 4096) with 32768; lia).
assert (Hd8 : 4096 * (len / 8 / 4096) <= len / 8) by (apply Z.mul_div_le; lia).
assert (Hd1 : 8 * (len / 8) <= len) by (apply Z.mul_div_le; lia).
nia.
Qed.
