(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCe5.v, with its module paths changed and off_img's image bounds taken from the unit's own Reusable/YImgTop.v. *)
(* Modified by Theorem Labs, 2026-10: the empty-depot switch (DepotCfg.depot_has_trace) taken from proofs/libreac/fuzz_knock/lib/Reusable/YCe5.v at 88154566652a, hunk by hunk (provenance evidence/depot: depot-classes.tsv, depot_apply.py): hunks 2 3 4 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30; hunks 1 5 keep this file's text. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YCe5.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d DepotCfg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG08.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Export YM04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac appn := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, kImgLo in *.
Ltac zlia := appn; lia.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section j.
Variable segs : list Segment.
Lemma aview_rd_of : forall H mem, aview segs H mem = rd_of segs (mrestrict H mem).
Proof. intros H mem. reflexivity. Qed.
Lemma apresent_grows : forall H m m' a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|]. exfalso.
apply (Hg (Z_to_bv 64 a)); unfold mrestrict; rewrite Hh; [rewrite Hb; discriminate | exact E'].
Qed.
Lemma aview_some_of_apresent : forall H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma aview_keeps_vis : forall H m m' a,
mem_grows (mrestrict H m) (mrestrict H m') -> aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros H m m' a Hg. unfold aview, mbyte.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E.
- destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [cbn; intros _; discriminate|].
exfalso. exact (Hg _ ltac:(rewrite E; discriminate) E').
- destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [cbn; intros _; discriminate|]. intros Hx; exact Hx.
Qed.
Lemma aview_eq_of : forall H (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview segs H m' a = aview segs H m a.
Proof. intros H m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.
Lemma mrestrict_unrestrict_mem : forall (H : word -> bool) mem msr',
hclean H msr' -> mrestrict H (ms_mem (unrestrict H mem msr')) = ms_mem msr'.
Proof.
intros H mem msr' Hcl. pose proof (restrict_unrestrict_clean H mem msr' Hcl) as E.
apply (f_equal ms_mem) in E. exact E.
Qed.
End j.
Definition block_rng (b : Z * Z) : Z * Z := (fst b, req_size (snd b)).
Definition ablocks_fp (bl : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b, fst b + req_size (snd b))) bl.
Lemma inFP_ablocks_fp : forall bl p n i, In (p, n) bl -> 0 <= i < req_size n -> inFP (ablocks_fp bl) (p + i).
Proof.
intros bl p n i Hin Hi. exists (p, p + req_size n). split; [|cbn; lia].
unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) bl (p, n)). exact Hin.
Qed.
Lemma inFP_ablocks_fp_inv : forall bl a, inFP (ablocks_fp bl) a -> exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Proof.
intros bl a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn in Ha.
exists p, n. auto.
Qed.
Definition frame_rng (ly : alayout) (f : Z * Z) : Z * Z := (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f)).
Lemma req_size_pos : forall n, 0 <= n -> 1 <= req_size n /\ n <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; lia. Qed.
Lemma pairwise_app_l : forall {X} (R : X -> X -> Prop) l1 l2, pairwise R (l1 ++ l2) -> pairwise R l1 /\ pairwise R l2.
Proof.
intros X R l1 l2. induction l1 as [|x l1 IH]; cbn; intros H; [split; [exact I | exact H]|].
destruct H as [Hf Hp]. apply Forall_app in Hf as [Hf1 Hf2]. destruct (IH Hp) as [H1 H2]. repeat split; assumption.
Qed.
Lemma pairwise_In2 : forall {X} (R : X -> X -> Prop) l x y l1 l2 l3,
pairwise R l -> l = l1 ++ x :: l2 ++ y :: l3 -> R x y.
Proof.
intros X R l x y l1. revert l. induction l1 as [|z l1 IH]; intros l l2 l3 Hp ->; cbn in Hp.
- destruct Hp as [Hf _]. apply Forall_app in Hf as [_ Hf]. inversion Hf. assumption.
- destruct Hp as [_ Hp]. eapply IH; [exact Hp | reflexivity].
Qed.
Lemma pairwise_zdisjoint_split : forall l (x y : Z * Z),
pairwise zdisjoint l -> (exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3 \/ l = l1 ++ y :: l2 ++ x :: l3) -> zdisjoint x y.
Proof.
intros l x y Hp (l1 & l2 & l3 & [E|E]).
- exact (pairwise_In2 zdisjoint l x y l1 l2 l3 Hp E).
- pose proof (pairwise_In2 zdisjoint l y x l1 l2 l3 Hp E) as H. unfold zdisjoint in *. lia.
Qed.
Lemma in_split_2 : forall {X} (x y : X) l, In x l -> In y l -> x <> y ->
exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3 \/ l = l1 ++ y :: l2 ++ x :: l3.
Proof.
intros X x y l Hx Hy Hne. apply in_split in Hx as (a & b & ->).
apply in_app_or in Hy as [Hy | [Hy | Hy]]; [| exfalso; exact (Hne Hy) |].
- apply in_split in Hy as (c & d & ->). exists c, d, b. right. rewrite <- app_assoc. reflexivity.
- apply in_split in Hy as (c & d & ->). exists a, c, d. left. reflexivity.
Qed.
Section t.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation code := (as_code B).
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
Lemma blk_img : forall ly S W mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ in_img segs a.
Proof. intros ly S W mem md p n a HAR Hin Hr. apply (al_client_img _ _ LAWS ly S W mem md a HAR). left. exists p, n. auto. Qed.
Lemma frm_img : forall ly S W mem md cid pos a,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ in_img segs a.
Proof. intros ly S W mem md cid pos a HAR Hin Hr. apply (al_client_img _ _ LAWS ly S W mem md a HAR). right. left. exists cid, pos. auto. Qed.
Definition achain (ly : alayout) (rd : reader) (sp v : Z) (ch : list (Z * Z * Z)) : Prop :=
((v < alloc_ceiling \/ ly_top ly - 16 <= v \/ v mod 8 <> 0) /\ ch = [])
\/ (sp + 16 <= v /\ v < ly_top ly - 16 /\ v mod 8 = 0 /\ fpchain (rdword rd) v (ly_top ly) ch /\
Forall (fun r => sp + 16 <= fst (fst r)) ch).
Definition spine (ch : list (Z * Z * Z)) : list Z := map (fun r => snd (fst r)) ch.
Lemma achain_low : forall ly rd sp v, v < alloc_ceiling -> achain ly rd sp v [].
Proof. intros ly rd sp v Hv. left. split; [left; exact Hv | reflexivity]. Qed.
Lemma achain_ly_top : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch E H. unfold achain in *. rewrite E. exact H. Qed.
Lemma achain_lower : forall ly rd sp sp' v ch, achain ly rd sp v ch -> sp' <= sp -> achain ly rd sp' v ch.
Proof.
intros ly rd sp sp' v ch [H | (H1 & H2 & H3 & H4 & H5)] Hle; [left; exact H|]. right.
repeat (split; [first [zlia | assumption]|]). eapply Forall_impl; [|exact H5]. intros r Hr. cbn beta in Hr. zlia.
Qed.
Lemma fpchain_fps_increase : forall load bp top ch,
fpchain load bp top ch -> Forall (fun r => bp <= fst (fst r)) ch.
Proof.
intros load bp top ch. revert bp. induction ch as [|[[fp ra] nfp] ch IH]; intros bp H; [constructor|].
cbn in H. destruct H as (-> & Hal & H8 & H16 & Hra & Hrest). constructor; [cbn; zlia|].
destruct (bad_next bp top nfp) eqn:Hb; [subst ch; constructor|].
apply Forall_impl with (P := fun r => nfp <= fst (fst r)); [|apply IH, Hrest].
intros r Hr. unfold bad_next in Hb. apply Bool.orb_false_elim in Hb as [Hb _]. apply Bool.orb_false_elim in Hb as [Hb _].
apply Z.leb_gt in Hb. zlia.
Qed.
Lemma fpchain_ext : forall load load' bp top ch,
(forall a, bp - 16 <= a -> a + 8 <= top -> load' a = load a) -> bp < top ->
fpchain load bp top ch -> fpchain load' bp top ch.
Proof.
intros load load' bp top ch. revert bp. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hx Hbt H.
- cbn in H |- *. destruct H as (r & Hr & Hr4). exists r. split; [rewrite Hx by zlia; exact Hr | exact Hr4].
- cbn in H |- *. destruct H as (-> & Hal & H8 & H16 & Hra & Hrest).
repeat (split; [first [reflexivity | assumption | rewrite Hx by zlia; assumption]|]).
destruct (bad_next bp top nfp) eqn:Hb; [exact Hrest|].
unfold bad_next in Hb. apply Bool.orb_false_elim in Hb as [Hb _]. apply Bool.orb_false_elim in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
apply IH; [|zlia|exact Hrest]. intros a Ha1 Ha2. apply Hx; zlia.
Qed.
Lemma rdword_ext : forall (rd rd' : reader) a,
(forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a Hk. unfold rdword.
replace (rd' a) with (rd a) by (rewrite <- (Z.add_0_r a); symmetry; apply Hk; zlia).
rewrite !Hk by zlia. reflexivity.
Qed.
Lemma fpchain_fps_lt : forall load bp top ch,
fpchain load bp top ch -> bp < top -> Forall (fun r => fst (fst r) < top) ch.
Proof.
intros load bp top ch. revert bp. induction ch as [|[[fp ra] nfp] ch IH]; intros bp H Hb; [constructor|].
cbn in H. destruct H as (-> & Hal & H8 & H16 & Hra & Hrest). constructor; [cbn; zlia|].
destruct (bad_next bp top nfp) eqn:Hbn; [subst ch; constructor|]. apply (IH nfp Hrest).
unfold bad_next in Hbn. apply Bool.orb_false_elim in Hbn as [Hbn _]. apply Bool.orb_false_elim in Hbn as [_ Hbn].
apply Z.leb_gt in Hbn. zlia.
Qed.
Lemma achain_kept : forall ly rd rd' sp v ch lo,
achain ly rd sp v ch -> lo <= sp -> ly_top ly <= 2 ^ 64 ->
(forall a, lo <= a < 2 ^ 64 -> rd' a = rd a) ->
achain ly rd' sp v ch.
Proof.
intros ly rd rd' sp v ch lo Hc Hlo Htop Hk. destruct Hc as [Hc | (H1 & H2 & H3 & H4 & H5)]; [left; exact Hc|]. right.
repeat (split; [assumption|]). split; [|exact H5].
eapply fpchain_ext; [| |exact H4]; [|zlia]. intros a Ha1 Ha2.
apply rdword_ext; intros k Hk'; apply Hk; zlia.
Qed.
Lemma achain_chain_pre : forall ly rd sp v ch regs,
achain ly rd sp v ch -> alloc_ceiling <= spZ regs <= sp -> s0Z regs = v -> 4096 <= raZ regs ->
chain_pre ly rd regs ch.
Proof.
intros ly rd sp v ch regs Hc Hsp Hv Hra. unfold chain_pre. split; [exact Hra|]. rewrite Hv.
unfold frame0_ok. destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hf0 | Hf0].
2:{ destruct Hc as [(_ & ->) | (H1 & H2 & _)]; [reflexivity | exfalso; zlia]. }
unfold bad_next. destruct Hc as [([H|[H|H]] & ->) | (H1 & H2 & H3 & H4 & H5)].
- replace (v <=? spZ regs) with true by (symmetry; apply Z.leb_le; zlia). reflexivity.
- replace (ly_top ly - 16 <=? v) with true by (symmetry; apply Z.leb_le; zlia). rewrite Bool.orb_true_r. reflexivity.
- replace (v mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). cbn. rewrite Bool.orb_true_r. reflexivity.
- replace (v <=? spZ regs) with false by (symmetry; apply Z.leb_gt; zlia).
replace (ly_top ly - 16 <=? v) with false by (symmetry; apply Z.leb_gt; zlia).
replace (v mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact H3). cbn. split; [zlia | exact H4].
Qed.
Lemma achain_push : forall ly rd rd' fp v ra ch sp',
achain ly rd fp v ch -> ly_top ly <= 2 ^ 64 ->
(forall a, fp <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (fp - 8) = Some ra -> rdword rd' (fp - 16) = Some v -> 4096 <= ra ->
alloc_ceiling <= fp -> fp mod 8 = 0 -> fp < ly_top ly - 16 -> sp' + 16 <= fp ->
achain ly rd' sp' fp ((fp, ra, v) :: ch).
Proof.
intros ly rd rd' fp v ra ch sp' Hc Htop64 Hk H8 H16 Hra Hceil Hal Htop Hsp'.
pose proof (achain_kept ly rd rd' fp v ch fp Hc ltac:(zlia) Htop64 Hk) as Hc'.
right. split; [zlia|]. split; [zlia|]. split; [exact Hal|]. split.
- cbn. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|]. split; [exact Hra|].
unfold bad_next. destruct Hc' as [([H|[H|H]] & ->) | (H1 & H2 & H3 & H4 & H5)].
+ replace (v <=? fp) with true by (symmetry; apply Z.leb_le; zlia). reflexivity.
+ replace (ly_top ly - 16 <=? v) with true by (symmetry; apply Z.leb_le; zlia). rewrite Bool.orb_true_r. reflexivity.
+ replace (v mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). cbn. rewrite Bool.orb_true_r. reflexivity.
+ replace (v <=? fp) with false by (symmetry; apply Z.leb_gt; zlia).
replace (ly_top ly - 16 <=? v) with false by (symmetry; apply Z.leb_gt; zlia).
replace (v mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact H3). cbn. exact H4.
- constructor; [cbn; zlia|]. destruct Hc' as [(_ & ->) | (H1 & H2 & H3 & H4 & H5)]; [constructor|].
eapply Forall_impl; [|exact H5]. intros r Hr. cbn beta in Hr. zlia.
Qed.
Definition call_trace0 (pc0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
unwind_of_chain pc0 ((spZ regs, raZ regs, s0Z regs) :: ch).
Lemma call_trace_in : forall ly pc0 regs ch (U : list (list Z)),
In [pc0] U -> In (call_trace0 pc0 regs ch) U -> In (call_trace ly pc0 regs ch) U.
Proof. intros ly pc0 regs ch U H0 H1. unfold call_trace. destruct (frame0_ok ly regs); [exact H1 | exact H0]. Qed.
Lemma call_trace_cons : forall pc0 regs fp ra v ch,
call_trace0 pc0 regs ((fp, ra, v) :: ch) =
firstn kUnwindMax (pc0 :: (if raZ regs =? pc0 then [] else [raZ regs]) ++ (if ra =? pc0 then [] else [ra]) ++
flat_map (fun r => match r with (_, ra', _) => if ra' =? pc0 then [] else [ra'] end) ch).
Proof. intros. unfold call_trace0, unwind_of_chain. reflexivity. Qed.
Lemma call_trace_nil : forall pc0 regs,
call_trace0 pc0 regs [] = pc0 :: (if raZ regs =? pc0 then [] else [raZ regs]).
Proof.
intros. unfold call_trace0, unwind_of_chain. cbn [flat_map app]. rewrite app_nil_r.
unfold kUnwindMax. destruct (raZ regs =? pc0); reflexivity.
Qed.
Definition astk_ok (STK : Z) (ly : alayout) (sp0 : Z) : Prop :=
sp0 mod 16 = 0 /\ 0 <= STK /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly /\
ly_stk_hi ly <= 2 ^ 47 /\ ly_bot ly + STK < sp0 + ASTACK /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Definition afn_pre (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
AR segs B ly S W mem md /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
astk_ok STK ly (spZ regs) /\
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) /\
achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch /\
qtight S                                               .
Definition in_tmp_block (bl0 blc : list (Z * Z)) (a : Z) : Prop :=
exists b n, In (b, n) blc /\ ~ In (b, n) bl0 /\ b <= a < b + req_size n.
Definition in_frames (ly : alayout) (own : list (Z * Z)) (a : Z) : Prop :=
exists cid pos, In (cid, pos) own /\
(in_zr a (frame_addr ly cid pos, fs_frame_bytes cid) \/
in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)).
Definition ajournal (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
AR segs B ly' S' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ same_io md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
astk_ok STK ly sp0 /\
qtight S'                                              .
Lemma same_io_refl : forall md, same_io md md.
Proof. intros md. repeat split; reflexivity. Qed.
Lemma same_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof.
intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io.
rewrite B1, B2, B3, B4. auto.
Qed.
Lemma same_io_materialized : forall md md', same_but_materialized md md' -> same_io md md'.
Proof.
intros md md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
destruct md as [f [mp lz mt] io fs pr li ti sg sc]. repeat split; reflexivity.
Qed.
Lemma ajournal_init : forall STK FP ly S W regs mem md ch,
afn_pre STK ly S W regs mem md ch -> ajournal STK (spZ regs) FP ly S W mem md [] ly S W mem md 0.
Proof.
intros STK FP ly S W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply wle_refl|]. split; [apply same_io_refl|].
split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hpres|]. split; [exact Hstk | exact HQT].
Qed.
Lemma ajournal_mono_k : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k k',
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> k <= k' ->
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k'.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k k'
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & REST) Hkk.
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [zlia|]. split; [zlia|]. exact REST.
Qed.
Lemma aregs_preserved_of_st_ok : forall H E ss ms regs0 extra,
st_ok segs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 extra HS HA Hcs. exact (regs_preserved_of_st_ok segs E ss (restrict H ms) regs0 extra HS HA Hcs).
Qed.
Lemma aregs_preserved_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.
Lemma map_split_2 : forall {X Y} (f : X -> Y) l (x y : X),
(exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3 \/ l = l1 ++ y :: l2 ++ x :: l3) ->
exists m1 m2 m3, map f l = m1 ++ f x :: m2 ++ f y :: m3 \/ map f l = m1 ++ f y :: m2 ++ f x :: m3.
Proof.
intros X Y f l x y (l1 & l2 & l3 & [-> | ->]); exists (map f l1), (map f l2), (map f l3);
[left | right]; rewrite !map_app; cbn; rewrite !map_app; reflexivity.
Qed.
Lemma sep_blocks : forall ly S W mem md b m p n,
AR segs B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
zdisjoint (b, req_size m) (p, req_size n).
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (pairwise_zdisjoint_split _ (b, req_size m) (p, req_size n) Hp).
exact (map_split_2 (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ _ (in_split_2 _ _ _ H1 H2 Hne)).
Qed.
Lemma sep_block_frame : forall ly S W mem md b m cid pos,
AR segs B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
zdisjoint (b, req_size m) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof.
intros ly S W mem md b m cid pos HAR H1 H2.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
apply in_split in H1 as (l1 & l2 & E1). apply in_split in H2 as (f1 & f2 & E2).
eapply (pairwise_In2 zdisjoint _ _ _ (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
(map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2 ++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) f1)
(map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) f2) Hp).
rewrite E1, E2, !map_app. cbn. rewrite <- !app_assoc. cbn. reflexivity.
Qed.
Lemma sep_frames_pos : forall ly S W mem md f g l1 l2 l3,
AR segs B ly S W mem md -> frames S = l1 ++ f :: l2 ++ g :: l3 ->
zdisjoint (frame_rng ly f) (frame_rng ly g).
Proof.
intros ly S W mem md f g l1 l2 l3 HAR E.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [_ Hp].
rewrite E, !map_app in Hp. cbn in Hp. rewrite map_app in Hp. cbn in Hp.
exact (pairwise_In2 zdisjoint _ _ _ _ _ _ Hp eq_refl).
Qed.
Lemma frames_bounds : forall ly S W mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
in_app (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ Hf].
pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _). auto.
Qed.
Definition awr_byte (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z)) (ly : alayout) (own : list (Z * Z)) (a : Z) : Prop :=
(sp0 - STK <= a < sp0) \/
(inFP FP a /\ exists b n, In (b, n) blc /\ b <= a < b + req_size n) \/
in_tmp_block bl0 blc a \/
in_frames ly own a.
Lemma shadow_addr_bounds : forall x, 0 <= x < kHighMemEnd -> kLowMemEnd <= shadow_addr x < kHighShadowEnd.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. zlia. Qed.
Lemma asan_consts : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ kHighShadowEnd = 0x10007fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
kHighMemEnd = 0x800000000000 /\ kLowMemEnd = 0x7fff8000.
Proof. split; [exact (proj1 alloc_ceiling_val)|]. repeat split; reflexivity. Qed.
Lemma fs_frame_bytes_nonneg : forall c, 0 <= fs_frame_bytes c.
Proof. intros c. unfold fs_frame_bytes. apply Z.shiftl_nonneg. zlia. Qed.
Lemma shadow_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; zlia. Qed.
Lemma shadow_range_end : forall f n, 0 <= n -> shadow_addr f + n / 8 <= shadow_addr (f + n).
Proof.
intros f n Hn. unfold shadow_addr.
pose proof (Z.div_mod f 8 ltac:(zlia)). pose proof (Z.mod_pos_bound f 8 ltac:(zlia)).
pose proof (Z.div_mod n 8 ltac:(zlia)). pose proof (Z.mod_pos_bound n 8 ltac:(zlia)).
assert (f / 8 + n / 8 <= (f + n) / 8) by (apply Z.div_le_lower_bound; zlia). zlia.
Qed.
Lemma awr_byte_cases : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a HJ Hw.
destruct HJ as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & _) & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hw as [Hs | [(Hfp & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | Hof]]].
- split; [|left; zlia]. apply (al_stack _ _ LAWS lyc Sc Wc memc mdc a HAR).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). rewrite Elo, Ehi. zlia.
- destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin) as (_ & H4096 & Hceilb & [Hh1 Hh2] & Hb & _).
split; [exact (proj2 (Hb a Hr))|]. right; left. split; [exact (in_app_addr _ _ _ (conj Hh1 Hh2) Hr)|]. exists b, n. auto.
- destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin) as (_ & H4096 & Hceilb & [Hh1 Hh2] & Hb & _).
split; [exact (proj2 (Hb a Hr))|]. right; left. split; [exact (in_app_addr _ _ _ (conj Hh1 Hh2) Hr)|]. exists b, n. auto.
- destruct Hof as (cid & pos & Hin & Hr).
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR Hin') as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (frames_bounds lyc Sc Wc memc mdc cid pos HAR Hin') as (Hf0 & Hfc & _).
destruct Hr as [Hr | Hr].
+ unfold in_zr in Hr; cbn [fst snd] in Hr. split; [exact (proj2 (Hb a Hr))|].
right; right. exists cid, pos. split; [exact Hin|]. left. split; [exact (in_app_addr _ _ _ (conj Hh1 Hh2) Hr)|]. exact Hr.
+ unfold in_zr in Hr; cbn [fst snd] in Hr. split.
* specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia.
exact (proj2 Hsh).
* right; right. exists cid, pos. split; [exact Hin|]. right. split; [|exact Hr].
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)).
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)). zlia.
Qed.
Lemma ajournal_after_write : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply same_io_trans; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)]; [exact (Hs Hs') | zlia | zlia | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)].
- zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He. rewrite <- (F3 a Hi Hns He). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [intros a Ha; apply Hgr; apply Hpres, Ha|].
split; [exact Hstatic | exact HQT'].
Qed.
Lemma ajournal_exec : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
eapply (ajournal_after_write STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr Sc own HJ Heqw
ltac:(intros a Ha; eapply apresent_grows; [exact Hgr | exact Ha]) Hsame);
[intros a Ha; left; exact (HW a Ha) | | reflexivity | reflexivity | zlia | exact Hfrs | exact HQT].
eapply (al_frame _ _ LAWS); [exact HAR | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros HWa. exact (proj1 (awr_byte_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (HW _ HWa)) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh).
Qed.
Lemma same_but_materialized_wvb_any : forall m X, same_but_materialized m (with_vm_backing (m_vm_lazy m) X m).
Proof. intros m X. unfold same_but_materialized. rewrite m_vm_materialized_wvb. reflexivity. Qed.
Lemma ajournal_materialize : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k X,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k X HJ.
eapply (ajournal_exec STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc _ (fun _ => False) HJ);
[intros x _; reflexivity | apply mem_grows_refl | intros x _; reflexivity | apply same_but_materialized_wvb_any | intros a Ha; destruct Ha].
Qed.
Lemma find_segment_none : forall a, ~ in_img segs a -> find_segment segs a 1 = None.
Proof.
intros a Hn. induction segs as [|sg rest IH] in Hn |- *; [reflexivity|]. cbn.
destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
- exfalso. apply Hn. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
exists sg. split; [left; reflexivity | zlia].
- apply IH. intros (sg' & Hin & Hr). apply Hn. exists sg'. split; [right; exact Hin | exact Hr].
Qed.
Lemma seg_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> seg_rom segs (Z_to_bv 64 a) = None.
Proof.
intros a Ha Hn. unfold seg_rom, memory_read. cbn [Z.of_N].
rewrite unsigned_lit_small by zlia. rewrite (find_segment_none a Hn). reflexivity.
Qed.
Lemma mbyte_of_aview : forall H H' (m m' : word -> option byte) a,
aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma apresent_transfer : forall H H' (m m' : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img segs a ->
aview segs H' m' a = aview segs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha Hn E [Hh [b Hb]]. apply mbyte_of_aview in E. unfold apresent. unfold mbyte, mrestrict in E.
rewrite Hh, Hb in E. rewrite (seg_rom_none a Ha Hn) in E.
destruct (H' (Z_to_bv 64 a)); [discriminate|]. split; [reflexivity|].
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | discriminate].
Qed.
Lemma apresent_writable : forall H (m : word -> option byte) a,
apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma layout_le_mono : forall n m ly ly', (n <= m)%nat -> layout_le m ly ly' -> layout_le n ly ly'.
Proof.
intros n m ly ly' Hnm H. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
repeat (split; [assumption|]). intros r Hr. apply A17. zlia.
Qed.
Lemma sep_blocks_pos : forall ly S W mem md x y l1 l2 l3,
AR segs B ly S W mem md -> ablocks B ly S = l1 ++ x :: l2 ++ y :: l3 ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y l1 l2 l3 HAR E.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
rewrite E, !map_app in Hp. cbn in Hp. rewrite map_app in Hp. cbn in Hp.
exact (pairwise_In2 zdisjoint _ _ _ _ _ _ Hp eq_refl).
Qed.
Lemma ablocks_app : forall ly (l1 l2 : list (sptr * Z)),
map (fun b : sptr * Z => (sptr_addr B ly (fst b), snd b)) (l1 ++ l2) =
map (fun b : sptr * Z => (sptr_addr B ly (fst b), snd b)) l1 ++ map (fun b : sptr * Z => (sptr_addr B ly (fst b), snd b)) l2.
Proof. intros. apply map_app. Qed.
Lemma ajournal_sub : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
ajournal STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & HQT2) Hlo Hhi HF.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|]. split; [eapply same_io_trans; eassumption|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{   intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{   intros p n i H1 H2 Hi Hnf.
assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
intros Hf1. destruct (HF _ Hf1) as [[Hf _] | (b & m & Hbin & Hb0 & Hr)]; [exact (Hnf Hf)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{   intros a Hi Hns He. rewrite <- (F3 a Hi Hns He). exact (G3 a Hi Hns He). }
split.
{   intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
apply (G4 cid pos a HinC).
- unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
- intros Hf1. destruct (HF _ Hf1) as [[Hf _] | (b & m & Hbin & Hb0 & Hrb)]; [exact (Hnf Hf)|].
destruct (frames_bounds lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
pose proof (sep_block_frame lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd.
pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
destruct Hr as [Hr|Hr]; zlia. }
split.
{   intros p n i H1 H2 Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
destruct (HF _ Hf1) as [[Hf _] | (b & m & Hbin & Hb0 & Hr)]; [exact Hf|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{   intros a Ha.
destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
- eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha].
- eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha]. }
split; [exact Hstatic | exact HQT2].
Qed.
End t.
Definition off_img (a n : Z) : Prop := a + n <= IMG_LO \/ IMG_TOP <= a.
Definition zone2 (a n : Z) : Prop := off_img a n /\ (a + n <= 2147446784 \/ 17594333495296 <= a).
Lemma zone2_band : forall a n, zone2 a n -> a + n <= 2147446784 \/ 17594333495296 <= a. Proof. intros a n [_ H]; exact H. Qed.
Lemma zone2_img : forall a n, zone2 a n -> off_img a n. Proof. intros a n [H _]; exact H. Qed.
Lemma zone2_le : forall a n m, zone2 a m -> n <= m -> zone2 a n. Proof. intros a n m [H1 H2] Hle. unfold zone2, off_img in *. lia. Qed.
Definition frame_flag_lawP (segs : list Segment) (B : asyms) : Prop :=
forall ly S (W : world segs) mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
(app_addr (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)) /\
(4096 <= flag_addr ly cid pos /\ zone2 (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling).
Definition stack_malloc_progressP (B : asyms) : Prop :=
forall s cid, Wf (as_universe B) s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s').
Definition api_env (segs : list Segment) (B : asyms) : Prop :=
(0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd) /\
(forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a) /\
(In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B)).
Section a0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Let UNIV0 : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B) := proj2 (proj2 errno_low).
Let ERRIMG : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a := proj1 (proj2 errno_low).
Hypothesis ML : model_laws (as_universe B).
Local Notation code := (as_code B).
Local Notation afn_pre := (afn_pre segs B).
Local Notation ajournal := (ajournal segs B).
Definition acall_kept (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).
Lemma in_ablocks : forall ly S pa n,
In (pa, n) (ablocks B ly S) <-> exists q, sptr_addr B ly q = pa /\ In (q, n) (blocks S).
Proof.
intros ly S pa n. unfold ablocks. rewrite in_map_iff. split.
- intros ([q m] & E & Hin). cbn in E. injection E as <- <-. exists q. auto.
- intros (q & <- & Hin). exists (q, n). auto.
Qed.
Lemma secs_ext_length : forall s s', secs_ext s s' -> (length (st_secs s) <= length (st_secs s'))%nat.
Proof.
intros s s' H. destruct (length (st_secs s)) as [|n] eqn:E; [zlia|].
destruct (nth_error (st_secs s) n) as [sm|] eqn:En.
- destruct (H n sm En) as (sm' & Hn & _).
assert (Hlt : (n < length (st_secs s'))%nat) by (apply nth_error_Some; rewrite Hn; discriminate). zlia.
- apply nth_error_None in En. zlia.
Qed.
Lemma firstn_eq_length_le : forall {X} (l l' : list X) n, l = firstn n l' -> n = length l -> (length l <= length l')%nat.
Proof. intros X l l' n -> Hn. rewrite length_firstn. zlia. Qed.
Lemma map_eq_In : forall {X Y} (f g : X -> Y) l x, map f l = map g l -> In x l -> f x = g x.
Proof.
intros X Y f g l x. induction l as [|y l IH]; intros E Hin; [destruct Hin|].
cbn in E. injection E as E1 E2. destruct Hin as [<-|Hin]; [exact E1 | exact (IH E2 Hin)].
Qed.
Lemma call_effect_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 (Eb : Z -> Prop) FP1 nf k1,
AR segs B ly2 S2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ ascratch B stk regs a -> ~ Eb a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
AR segs B lyc Sc W memc mdc ->
astk_ok stk lyc (spZ regs) ->
frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
ajournal stk (spZ regs) FP1 lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 Eb FP1 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ Eb a -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H4 H5 H6. apply (Hfr a H6 H1 H2); [|exact H5]. unfold ascratch. intros [H|H]; [exact (H3 H) | exact (H4 H)]. }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|]. split; [exact Hwle2|]. split; [exact Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{   intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- zlia.
- intros He. destruct (HE a He) as (b & m & Hbm & Hr & _). pose proof (BLK b m a Hbm Hr). zlia.
- zlia. }
split.
{   intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- intros Herr. exact (blk_img _ _ LAWS _ _ _ _ _ p n (p + i) HAR H1 ltac:(zlia) (ERRIMG _ Herr)).
- intros He. destruct (HE _ He) as (b & m & Hbm & Hr & [Hf | Hnot]); [exact (Hnf Hf)|].
destruct Hbm as [Hbm|Hbm]; [exact (Hnot Hbm)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks segs B LAWS ly2 S2 W2 mem2 md2 b m p n HAR2 Hbm H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). pose proof asan_consts. zlia. }
split.
{   intros a Hi Hns He. pose proof (segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- exact He.
- intros Heb. destruct (HE a Heb) as (b & m & Hbm & Hr & _).
destruct Hbm as [Hbm|Hbm]; [exact (blk_img _ _ LAWS _ _ _ _ _ b m a HAR Hbm Hr Hi) | exact (blk_img _ _ LAWS _ _ _ _ _ b m a HAR2 Hbm Hr Hi)].
- zlia. }
split.
{   intros cid pos a Hin Hr Hnf.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia. exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- intros Herr. destruct Hr as [Hr|Hr]; [exact (frm_img _ _ LAWS _ _ _ _ _ cid pos a HAR Hin Hr (ERRIMG _ Herr)) | zlia].
- intros Heb. destruct (HE a Heb) as (b & m & Hbm & Hrb & _). pose proof (BLK b m a Hbm Hrb).
destruct Hr as [Hr|Hr]; [|zlia].
destruct Hbm as [Hbm|Hbm].
+ pose proof (sep_block_frame segs B LAWS lyc Sc W memc mdc b m cid pos HAR Hbm Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
+ pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 b m cid pos HAR2 Hbm Hin2) as Hd. rewrite Efa in Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- destruct Hr as [Hr|Hr]; zlia. }
split; [exact Hgone|]. split; [exact Hpres2|]. split; [exact Hstk | exact HQT2].
Qed.
Lemma acall_post_journal : depot_pick (
 forall lyc Sc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb : Z -> Prop) FP1 k1,
acall_post segs B ASTACK lyc Sc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
AR segs B lyc Sc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
ajournal ASTACK (spZ regs) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1
) (
 forall lyc Sc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb : Z -> Prop) FP1 k1,
acall_post segs B ASTACK lyc Sc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
AR segs B lyc Sc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
st_depot Sc <> [] ->
ajournal ASTACK (spZ regs) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1
).
Proof.
intros lyc Sc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 Eb FP1 k1 (HAR2 & Hly2 & Hwle2 & HP & Hio2 & Hfr & Hpres2) HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2.
lazymatch eval cbv in depot_has_trace with true => idtac | false => intros KDM; pose proof (depot_ok_mapped B lyc _ Sc (am_depot B lyc Sc _ (proj1 HAR)) KDM) as [KNB KSB]; apply (gle_mapped _ _ _ KNB KSB) in Hly2 end.
eapply (call_effect_journal ASTACK lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 Eb FP1 [] k1); try eassumption.
Qed.
Lemma acall_kept_of_journal : forall stk sp1 FP1 nf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 (E : Z -> Prop),
ajournal stk sp1 FP1 lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
AR segs B lyc Sc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
acall_kept lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros stk sp1 FP1 nf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 E
(HAR2 & Hly2 & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & HQT) HAR HFE Hlive.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact G1|]. split.
{ intros b m i Hb Hi HnE. apply (G2 b m i Hb (Hlive b m i Hb Hi HnE) Hi). intros Hf. exact (HnE (HFE _ Hf)). }
split; [exact G3|]. split.
{ intros cid pos a Hin Hr HnE. apply (G4 cid pos a); [cbn; exact Hin | exact Hr | intros Hf; exact (HnE (HFE _ Hf))]. }
split; [|exact Hpres].
intros a Ha Hs Hp. eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; [exact Ha | exact Hs] | exact Hp].
Qed.
Lemma aj_free_at : afree_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
HJ Hin Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks lyc Sc pa n) Hin) as (q & Hq & Hqin).
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc pa n HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; zlia).
lazymatch eval cbv in depot_has_trace with true => idtac | false =>
assert (KDM : st_depot Sc <> []) by (pose proof (am_alloc_depot B lyc Sc _ (proj1 HAR)) as AD; unfold am_alloc_depot_d in AD;
  apply AD; pose proof Hqin as HQB; unfold blocks in HQB;
  apply in_map_iff in HQB as (kq & _ & Hkq); apply filter_In in Hkq as [Hkq _]; exists kq; exact Hkq)
end.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (call_trace_in lyc _ regsT ch _ (proj2 UNIV0) Htr) as Htr'.
pose proof (ml_free _ ML Sc q n (call_trace lyc (pc_free_ra0 code) regsT ch) HWF Hev (or_intror Hqin) Htr') as HTOK.
pose proof (AFREE lyc Sc W regsT memT mdc q n ch HPRE (or_intror Hqin) ltac:(rewrite Hq; exact Ha0) Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [[] S2]. unfold free_post in HQ. cbn [fst snd] in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2) & _).
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hqnn Hnull)|].
cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (depot_ok_mapped B lyc _ Sc (am_depot B lyc Sc _ (proj1 HAR)) KDM) as [KNB KSB]; apply (gle_mapped _ _ _ KNB KSB) in Hly2 end.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2). rewrite Hbl2, map_app.
f_equal; apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n) :: map fc l2). rewrite Hsplit, map_app. cbn [map app].
replace (fc (q, n)) with (pa, n) by (subst fc; cbn [fst snd]; rewrite Hq; reflexivity). reflexivity. }
assert (Hlive : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n) ->
In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite Eab2. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- apply in_or_app. left. exact Hb.
- exfalso. injection Hb as <- <-. apply HnE. zlia.
- apply in_or_app. right. exact Hb. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
inFP [(pa, pa + req_size n)] (p + i)).
{ intros p m i Hp Hnp Hi. exists (pa, pa + req_size n). split; [left; reflexivity|]. cbn [fst snd].
destruct (Z_lt_le_dec (p + i) pa) as [H1|H1]; [exfalso; apply Hnp; apply (Hlive p m i Hp Hi); zlia|].
destruct (Z_lt_le_dec (p + i) (pa + req_size n)) as [H2|H2]; [zlia|]. exfalso; apply Hnp; apply (Hlive p m i Hp Hi); zlia. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ lazymatch eval cbv in depot_has_trace with true => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | | | exact HgoneC | exact HQT2] | false => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | | | exact HgoneC | exact HQT2 | exact KDM] end.
- exact (secs_ext_length _ _ Hsecs2).
- intros a [_ Ha]. rewrite Hq in Ha. exists pa, n. split; [left; exact Hin|]. split; [exact Ha|]. left.
exists (pa, pa + req_size n). split; [left; reflexivity | cbn; zlia]. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n) (ablocks B ly S)) as [H0|H0].
- left. split; [| exists pa, n; split; [exact Hin | zlia]].
replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right. exists pa, n. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|].
split; [exists (map fc l1), (map fc l2); split; [exact EabC | exact Eab2]|].
split; [exact Hfrs2|].
rewrite Hsp' in HJ1. replace (sp0 + o - ASTACK) with (sp0 + o - ASTACK) by zlia.
eapply acall_kept_of_journal; [exact HJ1 | exact HAR | | exact Hlive].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha.
Qed.
Lemma aj_free_null_at : depot_pick (
 afree_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
frames S2 = frames Sc /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
) (
 afree_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
st_depot Sc <> [] ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
frames S2 = frames Sc /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
lazymatch eval cbv in depot_has_trace with true => idtac | false => intros KDM end.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (call_trace_in lyc _ regsT ch _ (proj2 UNIV0) Htr) as Htr'.
pose proof (ml_free _ ML Sc PNull 0 (call_trace lyc (pc_free_ra0 code) regsT ch) HWF Hev (or_introl eq_refl) Htr') as HTOK.
pose proof (AFREE lyc Sc W regsT memT mdc PNull 0 ch HPRE (or_introl eq_refl) ltac:(cbn; exact Ha0) Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [[] S2]. unfold free_post in HQ. cbn [fst snd] in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2) & _).
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (depot_ok_mapped B lyc _ Sc (am_depot B lyc Sc _ (proj1 HAR)) KDM) as [KNB KSB]; apply (gle_mapped _ _ _ KNB KSB) in Hly2 end.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (Hperm : Permutation (blocks S2) (blocks Sc) \/ (exists l1' l2', blocks Sc = l1' ++ (PNull, 0) :: l2' /\ blocks S2 = l1' ++ l2')).
{ destruct Hsplit as [[_ E12] | E12]; [left; rewrite Hbl2, E12; apply Permutation_refl | right; exists l1, l2; auto]. }
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (HnoNull : forall l1' l2', blocks Sc = l1' ++ (PNull, 0) :: l2' -> False).
{ intros l1' l2' E1.
assert (Hin : In (0, 0) (ablocks B lyc Sc)).
{ unfold ablocks. change (In (0, 0) (map fc (blocks Sc))). rewrite E1, map_app. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc 0 0 HAR Hin) as (_ & H4096 & _). zlia. }
assert (Ebl : blocks S2 = blocks Sc).
{ destruct Hsplit as [[_ E12] | E12]; [rewrite Hbl2, E12; reflexivity | exfalso; exact (HnoNull l1 l2 E12)]. }
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Ebl. apply map_ext_in. exact Efc. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
inFP [] (p + i)).
{ intros p m i Hp Hnp Hi. exfalso. apply Hnp. rewrite Eab2. exact Hp. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ lazymatch eval cbv in depot_has_trace with true => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | | | exact HgoneC | exact HQT2] | false => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | | | exact HgoneC | exact HQT2 | exact KDM] end.
- exact (secs_ext_length _ _ Hsecs2).
- intros a [Hnn _]. exfalso. exact (Hnn eq_refl). }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia |].
intros a (rg & [] & _). }
split; [exact HP|].
split; [rewrite Eab2; apply Permutation_refl|].
split; [exact Hfrs2|].
rewrite Hsp' in HJ1.
eapply acall_kept_of_journal; [exact HJ1 | exact HAR | |].
- intros a (rg & [] & _).
- intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
Lemma asptr_null_dec : forall p : sptr, {p = PNull} + {p <> PNull}.
Proof. intros p. destruct p; [left; reflexivity | right; discriminate | right; discriminate | right; discriminate]. Qed.
Lemma aj_malloc_at : depot_pick (
 amalloc_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))))
) (
 amalloc_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
st_depot Sc <> [] ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))))
).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
lazymatch eval cbv in depot_has_trace with true => idtac | false => intros KDM end.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (call_trace_in lyc _ regsT ch _ (proj1 UNIV0) Htr) as Htr'.
pose proof (ml_malloc _ ML Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF Hev Hn Hlive Htr') as HTOK.
pose proof (AMALLOC lyc Sc W regsT memT mdc n ch HPRE Ha0 Hn Hlive Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (depot_ok_mapped B lyc _ Sc (am_depot B lyc Sc _ (proj1 HAR)) KDM) as [KNB KSB]; apply (gle_mapped _ _ _ KNB KSB) in Hly2 end.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Hsecsle : (length (st_secs Sc) <= length (st_secs S2))%nat) by exact (secs_ext_length _ _ Hsecs2).
destruct (asptr_null_dec p) as [-> | Hnn].
-
cbn in Hres.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Hbl. apply map_ext_in. exact Efc. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ lazymatch eval cbv in depot_has_trace with true => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2] | false => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2 | exact KDM] end.
- intros a [Hf _]. exfalso. exact (Hf eq_refl).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace (k + 1) with (k + 1) by zlia.
change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. left. split; [reflexivity|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal; [exact HJ1 | exact HAR | intros a (rg & [] & _) | ].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)] /\ ~ In p (map fst (blocks Sc))).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl. destruct Hbl' as [Hbl Hfresh].
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl, map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ lazymatch eval cbv in depot_has_trace with true => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2] | false => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2 | exact KDM] end.
- intros a [_ Ha]. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. right. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal; [exact HJ1 | exact HAR | intros a (rg & [] & _) | ].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
Let regime_ok_small' : forall s, st_nev s < EV_MAX -> regime_ok s := fun s H => or_introl H.
Lemma aj_malloc_at04 : depot_pick (
 amalloc_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))
) (
 amalloc_realizes segs B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
st_depot Sc <> [] ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))
).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
lazymatch eval cbv in depot_has_trace with true => idtac | false => intros KDM end.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre segs B lyc Sc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)  |]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (call_trace_in lyc _ regsT ch _ (proj1 UNIV0) Htr) as Htr'.
pose proof (ml_malloc_ns _ ML Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (regime_ok_small' _ Hev) Hn Hlive Htr') as HTOK.
pose proof (AMALLOC lyc Sc W regsT memT mdc n ch HPRE Ha0 Hn Hlive Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (atok_apath_flag _ _ _ tr r HTOK Hpath) as [HQ HNS]. rewrite (last_flag_true tr Hgf) in HNS.
destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (depot_ok_mapped B lyc _ Sc (am_depot B lyc Sc _ (proj1 HAR)) KDM) as [KNB KSB]; apply (gle_mapped _ _ _ KNB KSB) in Hly2 end.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Hsecsle : (length (st_secs Sc) <= length (st_secs S2))%nat) by exact (secs_ext_length _ _ Hsecs2).
destruct (asptr_null_dec p) as [-> | Hnn].
-
exfalso. discriminate (HNS eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)] /\ ~ In p (map fst (blocks Sc))).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl. destruct Hbl' as [Hbl Hfresh].
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl, map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal ASTACK (spZ regsT) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
{ lazymatch eval cbv in depot_has_trace with true => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2] | false => eapply acall_post_journal; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecsle | | | exact HQT2 | exact KDM] end.
- intros a [_ Ha]. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal; [exact HJ1 | exact HAR | intros a (rg & [] & _) | ].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
Lemma aj_malloc : depot_pick (
 amalloc_realizes segs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))))
) (
 amalloc_realizes segs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) ->
st_depot Sc <> [] ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))))
).
Proof.
intros AMALLOC W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o spw raw ch
HS Hpc Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr.
lazymatch eval cbv in depot_has_trace with true => idtac | false => intros KDM end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpc.
eapply aj_malloc_at; eassumption.
Qed.
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Lemma aj_stack_malloc_at : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal; [exact HJ1 | exact HAR | intros a (rg & [] & _) | ].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
Lemma afn_pre_at : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 (o : Z) ch1,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
afn_pre STK1 lyc Sc W regsc memc mdc ch1.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
split; [exact HAR|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|]. split.
- unfold astk_ok, ly_bot in *. rewrite Hsp, Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity.
- split; [|split; [exact Hch | exact HQT]]. intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia.
Qed.
Lemma ajournal_sub_init : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k STK1 sp1 FP1 (o : Z),
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
sp1 = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
ajournal STK1 sp1 FP1 lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k STK1 sp1 FP1 o HJ Hsp Hal Hneg Hstk1 Hbud.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply wle_refl|]. split; [apply same_io_refl|].
split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split.
- intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia.
- split; [|exact HQT]. unfold astk_ok, ly_bot in *. rewrite Hsp, Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity.
Qed.
Lemma aj_call : forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
(K : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 K
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
Lemma region_kept_stack_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs sp
STK sp0 FP ly S W0 mem md own k,
ajournal STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> sp1 <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs sp STK sp0 FP ly S W0 mem md own k
HJ1 HJ Hn Hsp1 Hlo Hhi Hw1 Hw2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply G1; zlia.
- intros _. apply (apresent_writable segs). apply Hpres. zlia.
Qed.
Lemma region_kept_block_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m,
ajournal STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) ->
0 <= lo -> hi <= req_size m -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m HJ1 Hn Hin Hin2 Hlo Hhi Hro HnF.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|zlia].
apply (mbyte_of_aview segs). replace a with (b + (a - b)) by zlia. apply (G2 b m (a - b) Hin Hin2); [zlia|].
replace (b + (a - b)) with a by zlia. apply HnF. exact Ha.
Qed.
Lemma ecall_pre_at : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc (o : Z),
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
ecall_pre segs B lyc Sc W regsc memc mdc.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc o HJ Hsp Hal Hneg Hbud Hra Hgp Htp.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
split; [exact HAR|]. split; [exact Hra|]. split; [rewrite Hsp, Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp; zlia|]. split; [rewrite Eshi, Hsp; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp in Ha; zlia|]. split; [exact Hgp | exact Htp].
Qed.
Lemma awr_byte_present : forall STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc k a,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc k a HJ Hw.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
split; [|exact (proj1 (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw))].
destruct Hw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (cid & pos & Hin & Hr)]]].
- apply Hpres. exact Hs.
- exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin))))) a Hr)).
- exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin))))) a Hr)).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR Hin') as (_ & _ & Hb & Hsh).
destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [exact (proj1 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj1 Hsh).
Qed.
Lemma shadow_hull_vis_of_block : forall ly S W mem md p m d n,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= d -> d + n <= p + req_size m -> 0 < n ->
shadow_hull_vis (aview segs (w_H W) mem) d n.
Proof.
intros ly S W mem md p m d n HAR Hin Hpd Hdn Hn s Hs.
destruct (al_shadow _ _ LAWS ly S W mem md p m HAR Hin) as [_ Hh]. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + req_size m - 1) ltac:(zlia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [zlia|]; apply Z.div_le_mono; zlia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). zlia.
Qed.
Lemma aj_intrin_at : forall op pc, aintrin_realizes segs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
destruct (awr_byte_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma amem_range_high : forall p n, 0 <= n -> (p + n <= 2147446784 \/ 17594333495296 <= p) -> p + n <= alloc_ceiling -> amem_range p n.
Proof.
intros p n H0 H1 H2. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range.
unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. destruct H1 as [H1|H1]; [left; lia | right; lia].
Qed.
Lemma amem_range_of_block : forall ly S W mem md p m a n,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> amem_range a n.
Proof.
intros ly S W mem md p m a n HAR Hin H1 H2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & Hc & [Hh Hh2] & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). zlia.
Qed.
Lemma aj_memcmp_at : forall pc, amemcmp_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y n HPRE Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma aj_bcmp_at : forall pc, abcmp_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a) by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma aj_free : afree_realizes segs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o spw raw ch
HS Hpc Hrv HJ Hin Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpc.
eapply aj_free_at; eassumption.
Qed.
End a0.
Section d0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Definition awr_ok (E : env) (rs : smem) (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z))
(ly : alayout) (own : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a.
Lemma awr_ok_nil : forall E STK sp0 FP bl0 blc ly own, awr_ok E [] STK sp0 FP bl0 blc ly own.
Proof. intros E STK sp0 FP bl0 blc ly own a (r & Hin & _). destruct Hin. Qed.
Lemma awr_ok_cons_ro : forall E r rs STK sp0 FP bl0 blc ly own,
r_whi r <= r_wlo r -> awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own Hro H a (r' & [<-|Hin] & Ha); [zlia|]. apply H. exists r'. auto.
Qed.
Lemma awr_ok_cons_stack : forall E r rs STK sp0 FP bl0 blc ly own n,
r_base r = Some n -> bv_unsigned (ew E n) = sp0 -> - STK <= r_wlo r -> r_whi r <= 0 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n Hb Hn Hlo Hhi H a (r' & [<-|Hin] & Ha).
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. zlia.
- apply H. exists r'. auto.
Qed.
Lemma awr_ok_cons_stack_off : forall E r rs STK sp0 FP bl0 blc ly own n d,
r_base r = Some n -> bv_unsigned (ew E n) = sp0 + d -> - STK <= d + r_wlo r -> d + r_whi r <= 0 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n d Hb Hn Hlo Hhi H a (r' & [<-|Hin] & Ha).
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. zlia.
- apply H. exists r'. auto.
Qed.
Lemma awr_ok_cons_block : forall E r rs STK sp0 FP bl0 blc ly own n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b -> In (b, m) blc ->
0 <= r_wlo r -> r_whi r <= req_size m -> (forall a, b + r_wlo r <= a < b + r_whi r -> inFP FP a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b m Hb Hn Hin Hlo Hhi Hfp H a (r' & [<-|Hin'] & Ha).
- right. left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. split; [apply Hfp; zlia|].
exists b, m. split; [exact Hin | zlia].
- apply H. exists r'. auto.
Qed.
Lemma awr_ok_cons_tmp : forall E r rs STK sp0 FP bl0 blc ly own n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b -> In (b, m) blc -> ~ In (b, m) bl0 ->
0 <= r_wlo r -> r_whi r <= req_size m ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b m Hb Hn Hin Hn0 Hlo Hhi H a (r' & [<-|Hin'] & Ha).
- right. right. left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha.
exists b, m. split; [exact Hin | split; [exact Hn0 | zlia]].
- apply H. exists r'. auto.
Qed.
Lemma awr_ok_cons_gen : forall E r rs STK sp0 FP bl0 blc ly own k b,
r_base r = Some k -> bv_unsigned (ew E k) = b ->
(forall a, b + r_wlo r <= a < b + r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own k b Hb Hk Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hk in Ha. apply Hw. zlia.
- apply H. exists r'. auto.
Qed.
Local Notation ajournal := (ajournal segs B).
Definition run_post_AJ (W : world segs) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
st_ok segs E ss' (restrict (w_H W) ms') ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_chain_AJ : forall W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJ W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_exec segs B LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_AJ : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJ W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJ; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_AJ : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJ W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJ; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Definition run_post_tok_AJ (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_chain_tok_AJ : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJ W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_exec segs B LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_tok_AJ : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJ W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJ; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_tok_AJ : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJ W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJ; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
End d0.
Section e0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ML : model_laws (as_universe B).
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis ASF : astack_free_law segs B.
Hypothesis frame_flag_law : frame_flag_lawP segs B.
Local Notation ajournal := (ajournal segs B).
Lemma fs_frame_bytes_pos : forall cid, 0 <= cid -> 64 <= fs_frame_bytes cid.
Proof. intros cid Hc. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by zlia. pose proof (Z.pow_pos_nonneg 2 cid). nia. Qed.
Lemma aj_flag_store : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
0 <= cid ->
(forall a, in_wrange E (ss_mem ss) a ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
(forall msr, st_ok segs E ss' msr -> mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
(forall ms' mat',
st_ok segs E ss' (restrict (w_H W) ms') ->
ajournal STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HS Hrun Hst HJ Hcid Hwr Hflag0 Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS'0 & Hfr).
assert (HS' : st_ok segs E ss' msr') by (destruct st; [exact HS'0 | destruct Hst | exact HS'0]). clear HS'0.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frame_flag_law lyc Sc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a -> aview segs (w_H W) memc' a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
pose proof (sep_frames_pos segs B LAWS lyc Sc W (ms_mem ms) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
assert (HAR' : AR segs B lyc (stack_free_state cid pos Sc) W memc' (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASF lyc Sc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
- unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 msr' HS'). reflexivity.
- intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
exact (proj1 (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k
memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) own' HJ Heqw
ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
+ intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
+ exact HAR'.
+ unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
+ reflexivity.
+ cbn. zlia.
+ etransitivity; [exact E2 | symmetry; exact E1].
+ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
End e0.
Section f0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma aview_byte : forall H mem a v,
aview segs H mem a = Some v -> exists b : byte, mbyte segs (mrestrict H mem) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. exists b. split; [reflexivity|]. split; [reflexivity|].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H0. cbn in H0. zlia.
Qed.
Lemma val_mem_of_rdword : forall H mem a v,
rdword (aview segs H mem) a = Some v -> val_mem segs (mrestrict H mem) a 8 v.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte in E0 as (c0 & M0 & -> & R0). apply aview_byte in E1 as (c1 & M1 & -> & R1).
apply aview_byte in E2 as (c2 & M2 & -> & R2). apply aview_byte in E3 as (c3 & M3 & -> & R3).
apply aview_byte in E4 as (c4 & M4 & -> & R4). apply aview_byte in E5 as (c5 & M5 & -> & R5).
apply aview_byte in E6 as (c6 & M6 & -> & R6). apply aview_byte in E7 as (c7 & M7 & -> & R7).
rewrite ?Z.add_0_r in M0.
set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; zlia).
assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YO0f.le_byte v 8 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; zlia).
rewrite Z.shiftr_div_pow2 by zlia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; zlia | zlia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; zlia | zlia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |zlia];
[ change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r
| change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 | change (Z.of_nat 4) with 4
| change (Z.of_nat 5) with 5 | change (Z.of_nat 6) with 6 | change (Z.of_nat 7) with 7 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; subst v; zlia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; subst v; zlia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; subst v; zlia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
(bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; subst v; zlia.
- rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
(bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; subst v; zlia.
- rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
(bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; subst v; zlia.
- rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
(bv_unsigned c7)); cbn; subst v; zlia.
- rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
0); cbn; subst v; zlia.
Qed.
Lemma val_mem_byte0 : forall (m : word -> option byte) a n v,
val_mem segs m a (S n) v -> val_mem segs m a 1 (v mod 256).
Proof.
intros m a n v H k Hk. assert (k = 0%nat) as -> by zlia. specialize (H 0%nat ltac:(zlia)).
change (Z.of_nat 0) with 0 in *. rewrite H. f_equal. unfold YO0f.le_byte.
replace (8 * Z.of_nat 0) with 0 by zlia. rewrite !Z.shiftr_0_r.
replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. rewrite !Z.mod_mod by zlia. f_equal. symmetry.
apply Znumtheory.Zmod_div_mod; [zlia | apply Z.pow_pos_nonneg; zlia |].
replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by zlia. rewrite Z.pow_add_r by zlia.
change (2 ^ 8) with 256. apply Z.divide_factor_l.
Qed.
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat k)); [apply Hv, Hkn|]. apply Hk. zlia.
Qed.
Lemma shent_ok_of_block : forall ly S W mem md E Bx (m : nat) p n lo hi,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = p -> 0 <= lo -> lo <= hi <= req_size n ->
shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E Bx m p n lo hi HAR Hin HB Hm Hlo Hhi.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; zlia].
eapply block_shadow_range; [exact Hbs | zlia | zlia].
-
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
Lemma shent_app_of_block : forall ly S W mem md E Bx (m : nat) q p n wlo whi M,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + wlo -> wlo < whi -> q + whi <= p + req_size n ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof.
intros ly S W mem md E Bx m q p n wlo whi M HAR Hin HB Hm Hlo Hlt Hhi.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. split.
- apply range_addressable_nil. zlia.
- destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
Lemma shent_app_of_frame : forall ly S W mem md E Bx (m : nat) q cid pos wlo whi M,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> frame_addr ly cid pos <= q + wlo -> wlo < whi ->
q + whi <= frame_addr ly cid pos + fs_frame_bytes cid ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof.
intros ly S W mem md E Bx m q cid pos wlo whi M HAR Hin HB Hm Hlo Hlt Hhi.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. split.
- apply range_addressable_nil. zlia.
- destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Happ).
intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
Lemma shent_app_of_high : forall E Bx (m : nat) q wlo whi M,
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> kHighMemBeg <= q + wlo -> wlo < whi ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof.
intros E Bx m q wlo whi M HB Hm Hlo Hlt.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. split.
- apply range_addressable_nil. zlia.
- intros a Ha. unfold SHADOW_OFF, kHighMemBeg in *. zlia.
Qed.
Lemma shent_app_of_app : forall E Bx (m : nat) q wlo whi M,
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> (q + whi <= kLowShadowBeg \/ kHighMemBeg <= q + wlo) -> wlo < whi ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof.
intros E Bx m q wlo whi M HB Hm Happ Hlt.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. split.
- apply range_addressable_nil. zlia.
- intros a Ha. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. zlia.
Qed.
Lemma val_mem_agree : forall (m m' : word -> option byte) a n v,
val_mem segs m a n v -> val_mem segs m' a n v ->
forall k, 0 <= k < Z.of_nat n -> mbyte segs m' (a + k) = mbyte segs m (a + k).
Proof.
intros m m' a n v H1 H2 k Hk. replace k with (Z.of_nat (Z.to_nat k)) by zlia.
rewrite (H1 (Z.to_nat k) ltac:(zlia)), (H2 (Z.to_nat k) ltac:(zlia)). reflexivity.
Qed.
Lemma sep_blocks_perm : forall ly S W mem md x y l,
AR segs B ly S W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- pose proof (sep_blocks_pos segs B LAWS ly S W mem md y x b1 b2 a2 HAR ltac:(rewrite E1, E2, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint in *. zlia.
- exact (sep_blocks_pos segs B LAWS ly S W mem md x y a1 b1 b2 HAR ltac:(rewrite E1, E2; reflexivity)).
Qed.
Lemma region_kept_stack_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S W0 mem md own ly2 S2 md2 k,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S W0 mem md own ly2 S2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply K1; zlia.
- intros _. apply (apresent_writable segs). apply Hpres. zlia.
Qed.
Lemma region_kept_val : forall E (m m' : word -> option byte) lo (n : nat) v wlo whi cs,
val_mem segs m lo n v -> val_mem segs m' lo n v -> whi <= wlo ->
region_kept segs E m m' (YP09.mkRegion None lo (lo + Z.of_nat n) wlo whi cs).
Proof.
intros E m m' lo n v wlo whi cs H1 H2 Hro.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; [|zlia].
replace a with (lo + (a - lo)) by zlia. apply (val_mem_agree m m' lo n v H1 H2). zlia.
Qed.
Lemma region_kept_block_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b m,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) ->
0 <= lo -> hi <= req_size m -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m (_ & K2 & _) Hn Hin Hlo Hhi Hro HnE.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|zlia].
apply (mbyte_of_aview segs). replace a with (b + (a - b)) by zlia. apply (K2 b m (a - b) Hin); [zlia|].
replace (b + (a - b)) with a by zlia. apply HnE. exact Ha.
Qed.
Local Notation ajournal := (ajournal segs B).
Lemma val_mem_entry_block : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p m a (n : nat) v,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
In (p, m) (ablocks B ly S) -> In (p, m) (ablocks B ly' S') -> p <= a -> a + Z.of_nat n <= p + req_size m ->
(forall x, a <= x < a + Z.of_nat n -> ~ inFP FP x) ->
val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W') mem') a n v.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p m a n v HJ H1 H2 Hpa Han HnF Hv.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
eapply val_mem_kept; [|exact Hv]. intros i Hi.
replace (a + i) with (p + (a + i - p)) by zlia. apply (F2 p m (a + i - p) H1 H2); [zlia|].
replace (p + (a + i - p)) with (a + i) by zlia. apply HnF. zlia.
Qed.
Lemma val_mem_entry_frame : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a (n : nat) v,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
In (cid, pos) (frames S) -> frame_addr ly cid pos <= a -> a + Z.of_nat n <= frame_addr ly cid pos + fs_frame_bytes cid ->
(forall x, a <= x < a + Z.of_nat n -> ~ inFP FP x) ->
val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W') mem') a n v.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a n v HJ Hin Hfa Han HnF Hv.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
eapply val_mem_kept; [|exact Hv]. intros i Hi. apply (F4 cid pos (a + i) Hin).
- left. unfold in_zr, frame_rng. cbn [fst snd]. zlia.
- apply HnF. zlia.
Qed.
Lemma range_addressable_entry_frame : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a n,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos <= a -> a + n <= frame_addr ly cid pos + fs_frame_bytes cid ->
frame_addr ly cid pos mod 8 = 0 ->
(forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
AR segs B ly S W mem md ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n ->
range_addressable (aview segs (w_H W') mem') SHADOW_OFF a n.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a n HJ Hin Hcid Hfa Han Hal8 HFP HAR0 Hra x Hx.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR0 Hin) as (Hf0 & Hfc & Hfh).
assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
{ unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by zlia.
replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by zlia. apply Z_mod_mult. }
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 8 ltac:(zlia)) as Df. pose proof (Z.div_mod bs 8 ltac:(zlia)) as Db.
assert (Hq : f / 8 <= x / 8) by (apply Z.div_le_mono; zlia).
assert (Hq2 : x / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; zlia).
pose proof (shadow_addr_bounds x ltac:(zlia)) as Hsx.
destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
rewrite <- Hs. apply (F4 cid pos _ Hin).
- right. unfold in_zr. cbn [fst snd]. unfold shadow_of_addr, shadow_addr in *. subst f bs. zlia.
- intros HF. pose proof (HFP _ HF). unfold shadow_of_addr, shadow_addr, SHADOW_OFF in *. zlia.
Qed.
Lemma range_addressable_of_block : forall ly S W mem md p m a n,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md p m a n HAR Hin Hpa Han.
destruct (al_shadow _ _ LAWS ly S W mem md p m HAR Hin) as [Hbs _].
destruct (Z_lt_le_dec 0 n); [|apply range_addressable_nil; zlia].
eapply block_shadow_range; [exact Hbs | zlia | zlia].
Qed.
Lemma shent_ok_of_range : forall H mem E Bx (mt : nat) a n p lo hi,
range_addressable (aview segs H mem) SHADOW_OFF a n ->
U E Bx = SHADOW_OFF -> U E (SOff mt 0) = p -> a <= p + lo -> p + hi <= a + n ->
(forall x, p + Z.min lo hi <= x < p + Z.max lo hi -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
shent_ok segs Bx E (mrestrict H mem) (mkSHE mt lo hi).
Proof.
intros H mem E Bx mt a n p lo hi Hra HB Hm Hlo Hhi Happ.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
split; [|exact Happ].
destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; zlia].
eapply range_addressable_sub; [exact Hra | zlia | zlia].
Qed.
Lemma acall_kept_mono_E : forall lyc Sc W memc W2 mem2 slo shi (E E' : Z -> Prop),
acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> (forall a, E a -> E' a) ->
acall_kept segs B lyc Sc W memc W2 mem2 slo shi E'.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E E' (K1 & K2 & K3 & K4 & K5 & K6) HEE.
split; [exact K1|]. split; [intros b m i Hb Hi Hn; apply (K2 b m i Hb Hi); intros He; exact (Hn (HEE _ He))|].
split; [exact K3|]. split; [intros cid pos a Hf Hz Hn; apply (K4 cid pos a Hf Hz); intros He; exact (Hn (HEE _ He))|].
split; [exact K5 | exact K6].
Qed.
Lemma awr_byte_mono : forall STK sp0 FP bl0 blc blc' ly own a,
awr_byte STK sp0 FP bl0 blc ly own a -> (forall b n, In (b, n) blc -> b <= a < b + req_size n -> In (b, n) blc') ->
awr_byte STK sp0 FP bl0 blc' ly own a.
Proof.
intros STK sp0 FP bl0 blc blc' ly own a [H | [[Hf (b & n & Hin & Hb)] | [(b & n & Hin & Hn0 & Hb) | H]]] Hsub.
- left. exact H.
- right. left. split; [exact Hf|]. exists b, n. split; [exact (Hsub b n Hin Hb) | exact Hb].
- right. right. left. exists b, n. split; [exact (Hsub b n Hin Hb) | split; [exact Hn0 | exact Hb]].
- right. right. right. exact H.
Qed.
Definition aftok (FP : list (Z * Z)) (bl0 : list (Z * Z)) (b : Z * Z) : Prop :=
In b bl0 -> forall i, 0 <= i < req_size (snd b) -> inFP FP (fst b + i).
Lemma aftok_new_block : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
aftok FP (ablocks B ly S) (res, n).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n HJ HAR2 Ebl Hn H0 i Hi. cbn [fst snd] in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B lyc Sc)) as [Hc | Hc].
- exfalso. apply in_split in Hc as (l1 & l2 & E1).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbn; zlia). zlia.
- exact (Hgone res n i H0 Hc Hi).
Qed.
Lemma awr_new_block : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
In (res, n) blc -> 0 <= i < req_size n ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq HJ HAR2 Ebl Hn Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B ly S)) as [H0 | H0].
-
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B lyc Sc)) as [Hc | Hc].
+ exfalso. apply in_split in Hc as (l1 & l2 & E1).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbn; zlia). zlia.
+ right. left. split; [exact (Hgone res n i H0 Hc Hi)|]. exists res, n. split; [exact Hin | zlia].
- right. right. left. exists res, n. split; [exact Hin|]. split; [exact H0 | zlia].
Qed.
Lemma ast_ok_add_region : forall E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrwf Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hrwf, Hwf; reflexivity|]. split; [constructor; assumption|]. split; assumption.
Qed.
Lemma obl_of_range : forall H mem E Bx ux len a n,
range_addressable (aview segs H mem) SHADOW_OFF a n ->
U E Bx = SHADOW_OFF -> a <= ux -> ux + len <= a + n ->
range_addressable (rd_of segs (mrestrict H mem)) (U E Bx) ux len.
Proof.
intros H mem E Bx ux len a n Hra HB Hlo Hhi. rewrite HB. rewrite <- (aview_rd_of segs).
eapply range_addressable_sub; [exact Hra | zlia | zlia].
Qed.
Lemma obl_of_block : forall ly S W mem md E Bx ux len p m,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
U E Bx = SHADOW_OFF -> p <= ux -> ux + len <= p + req_size m ->
range_addressable (rd_of segs (mrestrict (w_H W) mem)) (U E Bx) ux len.
Proof.
intros ly S W mem md E Bx ux len p m HAR Hin HB Hlo Hhi.
eapply obl_of_range; [exact (range_addressable_of_block ly S W mem md p m ux len HAR Hin Hlo Hhi) | exact HB | zlia | zlia].
Qed.
Definition bsum (l : list (Z * Z)) : Z := fold_right (fun b acc => snd b + acc) 0 l.
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. intros l1 l2. unfold bsum. induction l1 as [|b l1 IH]; cbn; [reflexivity | rewrite IH; zlia]. Qed.
Lemma bsum_cons : forall b l, bsum (b :: l) = snd b + bsum l.
Proof. intros. reflexivity. Qed.
Lemma bsum_perm : forall l1 l2, Permutation l1 l2 -> bsum l1 = bsum l2.
Proof.
intros l1 l2 HP. induction HP; [reflexivity | rewrite !bsum_cons; zlia | rewrite !bsum_cons; zlia | zlia].
Qed.
Lemma blocks_bytes_bsum : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks, bsum.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.
Lemma call_trace_of_spine : forall pc0 regs ch,
call_trace0 pc0 regs ch =
firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) (raZ regs :: spine ch)).
Proof.
intros pc0 regs ch. unfold call_trace0, unwind_of_chain, spine. f_equal. cbn [flat_map]. f_equal. f_equal.
induction ch as [|[[a r] b] ch IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
End f0.
End e.
Definition BAND_SPAN : Z * Z := (0x7fff8000, 0x7fff8000 + 17592186044416 - 1).
Definition app_entries (G : facts) (rs : smem) : list shent :=
flat_map (fun r => match YP09.r_base r, window_itv G r with
| Some m, Some w =>
if itv_disjoint w (Some BAND_SPAN) then []
else match w with
| Some (l, h) => if ((fst BAND_SPAN <=? l) && (h <=? snd BAND_SPAN))%bool then [] else [mkSHE m (YP09.r_whi r) (YP09.r_wlo r)]
| None => [mkSHE m (YP09.r_whi r) (YP09.r_wlo r)]
end
| _, _ => []
end) rs.
Ltac azlit_tac := cbv; first [reflexivity | discriminate | (intros; discriminate) | tryif lf2_goal_closed then first [ solve [YM03.lf_prune0; zlia] | tryif YM03.lf_prune0 then fail else zlia ] else zlia].
Ltac awr_ok_tac :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply awr_ok_cons_stack; [reflexivity | | azlit_tac | azlit_tac |] ].
Ltac aj_laws := lazymatch goal with H : AR_laws _ _ |- _ => H | _ => fail "aj_*: no hypothesis  AR_laws segs B" end.
Ltac aj_segs_low := lazymatch goal with H : forall a, in_img _ a -> 0 <= a < kLowMemEnd |- _ => H
| _ => fail "aj_*: no hypothesis  forall a, in_img segs a -> 0 <= a < kLowMemEnd" end.
Ltac aj_wx := lazymatch goal with H : wx_segs_nowrap _ |- _ => H | _ => fail "aj_*: no hypothesis  wx_segs_nowrap segs" end.
Ltac aj_after_run HS HJ :=
let ms' := fresh "ms" in let mat' := fresh "mat" in
let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat' HS HJ HF HFr HG;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac aj_run tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_AJ segs _ HL HSL tbl tblok HWX W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ]
end
end
| _ => fail "aj_run: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_flag tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
let HML := lazymatch goal with H : model_laws _ |- _ => H | _ => fail "aj_run_flag: no model_laws hypothesis" end in
let HASF := lazymatch goal with H : astack_free_law _ _ |- _ => H | _ => fail "aj_run_flag: no astack_free_law hypothesis" end in
let HFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H | _ => fail "aj_run_flag: no frame_flag_lawP hypothesis" end in
eapply (aj_flag_store segs _ HL HSL HML tbl tblok HWX HASF HFFL W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ]
end
end
| _ => fail "aj_run_flag: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_to tblok HS HJ stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_to_AJ segs _ HL HSL tbl tblok HWX W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; cbv beta iota; aj_after_run HS HJ ]
end
end
| _ => fail "aj_run_to: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_after_run_tok HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac env_agree_chain HAE :=
first [ exact HAE
| apply env_agree_havoc_ge; [cbv; zlia | env_agree_chain HAE]
| eapply env_agree_trans; [ | eapply env_agree_le; [ | apply env_agree_ewset ]; cbv; zlia ]; env_agree_chain HAE ].
Ltac aj_run_tok tblok HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok segs tbl K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok segs tbl K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_tok_AJ segs _ HL HSL tbl tblok HWX W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
aj_after_run_tok HS HJ SHOK ]
end
end end
| _ => fail "aj_run_tok: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_to_tok tblok HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_to_tok_AJ segs _ HL HSL tbl tblok HWX W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
aj_after_run_tok HS HJ SHOK ]
end
end end
| _ => fail "aj_run_to_tok: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
