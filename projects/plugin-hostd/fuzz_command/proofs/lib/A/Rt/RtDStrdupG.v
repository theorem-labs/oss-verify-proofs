(* The model-level steps of the walk of plugin-hostd/fuzz_command's strdup entry that no file of this tree holds:
   an [amreal] post strengthened by the model's own [atok] post of the same itree, the allocator's own post as the
   model laws give it, and the facts about the block the allocation returns, the source bytes and the stack that
   the leaf of RtAlloc.v's astrdup_realizes needs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG07 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAlloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* One induction over the itree carries the model's own post to every leaf of [amreal]: the two statements run
   over the same tree, so each request of the one is the matching request of the other. *)
Lemma amreal_and_tok {R} : forall (t : itree astate R) (W : world tfibsegs) c
(Q : R -> world tfibsegs -> config -> Prop) (P : bool -> R -> Prop) (ns : bool),
amreal tfibsegs t W c Q -> atok ns t P ->
amreal tfibsegs t W c (fun r W' c' => Q r W' c' /\ exists b, P b r).
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q P ns H HT; cbn in *.
- eapply SRr_mono; [exact H|]. intros W' c' _ H'. split; [exact H'|]. exists ns. exact HT.
- destruct HT as [Hreq HK]. eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc);
exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|];
split; [exact Hr|]; split; [exact Hz|];
intros i Hi; eapply IH; [apply Hc, Hi | apply HK, Ha]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | apply HK, Hz].
- exact H.
- exact I.
Qed.

(* A byte the whole step leaves with the same view, and that the image does not hold, stays present. *)
Lemma apresent_of_view : forall (H H' : word -> bool) (m m' : word -> option byte) a,
seg_rom tfibsegs (Z_to_bv 64 a) = None ->
aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Hrom Hv Hp.
pose proof (AE2y.aview_some_of_apresent H m a Hp) as Hsome.
rewrite <- Hv in Hsome.
unfold apresent.
unfold aview, mbyte, mrestrict in Hsome.
destruct (H' (Z_to_bv 64 a)) eqn:Eh'.
- rewrite Hrom in Hsome. cbn in Hsome. exfalso. apply Hsome. reflexivity.
- destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Eb'.
+ split; [reflexivity|]. exists b'. reflexivity.
+ rewrite Hrom in Hsome. cbn in Hsome. exfalso. apply Hsome. reflexivity.
Qed.

Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The allocator's step, as the model laws give it: [AR] carries both [Wf] and [universe_ok]. *)
Lemma amalloc_tok : forall ly S (W : world tfibsegs) mem md n tr,
AR tfibsegs B ly S W mem md -> aregime S ->
0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> tr_admit (as_universe B) S tr ->
atok true (malloc n tr S) (malloc_post (as_universe B) S n).
Proof.
intros ly S W mem md n tr HAR HREG Hn Hlive Htr. pose proof (proj1 HAR) as HM.
exact (malloc_ok (as_universe B) S n tr (am_universe B ly S _ HM) (am_wf B ly S _ HM) HREG Hn Hlive Htr).
Qed.

(* The block list after the allocation, with the new block last. *)
Lemma ablocks_snoc : forall ly ly1 S S1 (W : world tfibsegs) mem md p n,
AR tfibsegs B ly S W mem md -> layout_le (length (st_secs S)) ly ly1 ->
blocks S1 = blocks S ++ [(p, n)] ->
ablocks B ly1 S1 = ablocks B ly S ++ [(sptr_addr B ly1 p, n)].
Proof.
intros ly ly1 S S1 W mem md p n HAR Hle HB.
unfold ablocks. rewrite HB, map_app. cbn [map].
f_equal. exact (proj1 (al_layout _ _ LAWS ly S W mem md ly1 HAR Hle)).
Qed.

(* What AR_blocks_law says about one live block. *)
Lemma dup_blk_facts : forall ly1 S1 (W1 : world tfibsegs) mem1 md1 dst n,
AR tfibsegs B ly1 S1 W1 mem1 md1 -> In (dst, n) (ablocks B ly1 S1) ->
(forall a, dst <= a < dst + req_size n -> apresent (w_H W1) mem1 a /\ ~ aowned B ly1 S1 a) /\
in_app dst (req_size n) /\ dst mod 16 = 0 /\ 4096 <= dst /\ dst + req_size n <= alloc_ceiling /\
0 <= n < MALLOC_MAX.
Proof.
intros ly1 S1 W1 mem1 md1 dst n HAR Hin.
destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 dst n HAR Hin) as (H16 & H4k & Hceil & Happ & Hby & _ & Hn).
split; [exact Hby|]. split; [exact Happ|]. split; [exact H16|]. split; [exact H4k|].
split; [exact Hceil | exact Hn].
Qed.

(* A source byte of the entry lies where the allocator never takes: it is unowned before and after the
   allocation, and it is not a byte of the block the allocation returns. The three cases of adup_src_kept
   (RtAlloc.v:61-64) are the three the journal of a program walk carries across a call. *)
Lemma dup_src_outside : forall ly S (W : world tfibsegs) mem md ly1 S1 (W1 : world tfibsegs) mem1 md1 dst n a,
AR tfibsegs B ly S W mem md -> AR tfibsegs B ly1 S1 W1 mem1 md1 ->
layout_le (length (st_secs S)) ly ly1 ->
ablocks B ly1 S1 = ablocks B ly S ++ [(dst, n)] ->
adup_src_kept tfibsegs B ly S a ->
~ aowned B ly S a /\ ~ aowned B ly1 S1 a /\ ~ (dst <= a < dst + req_size n).
Proof.
intros ly S W mem md ly1 S1 W1 mem1 md1 dst n a HAR HAR1 Hle HBL (Herr & Hcase).
assert (Hnew : In (dst, n) (ablocks B ly1 S1)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
destruct (dup_blk_facts ly1 S1 W1 mem1 md1 dst n HAR1 Hnew) as (Hby & Happ & _ & H4k & Hceil & _).
pose proof (am_layout B ly1 S1 _ (proj1 HAR1)) as HLY1.
destruct Hcase as [[Himg Hown] | [Hstk | (b & m & Hbm & Hin)]].
- (* a byte of the image the runtime does not own *)
assert (N0 : ~ aowned B ly S a).
{ intros HO. apply Hown. exact (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR Himg) HO). }
assert (N1 : ~ aowned B ly1 S1 a).
{ intros HO. apply Hown. exact (proj1 (al_owned_image _ _ LAWS ly1 S1 W1 mem1 md1 a HAR1 Himg) HO). }
split; [exact N0|]. split; [exact N1|]. intros Hblk.
exact (proj2 (al_client_img _ _ LAWS ly1 S1 W1 mem1 md1 a HAR1
(or_introl (ex_intro _ dst (ex_intro _ n (conj Hnew Hblk))))) Himg).
- (* a byte of the real stack *)
pose proof Hle as Hle'.
assert (Hlo1 : ly_stk_lo ly1 = ly_stk_lo ly).
{ unfold layout_le in Hle. tauto. }
assert (Hhi1 : ly_stk_hi ly1 = ly_stk_hi ly).
{ unfold layout_le in Hle. tauto. }
split; [exact (al_stack _ _ LAWS ly S W mem md a HAR Hstk)|].
split; [apply (al_stack _ _ LAWS ly1 S1 W1 mem1 md1 a HAR1); rewrite Hlo1, Hhi1; exact Hstk|].
intros Hblk. pose proof (lo_stk_ceil ly1 HLY1) as Hceil1. rewrite Hlo1 in Hceil1.
unfold ASAN_CEIL in Hceil1. lia.
- (* a byte of a live block *)
assert (Hin1 : In (b, m) (ablocks B ly1 S1)) by (rewrite HBL; apply in_or_app; left; exact Hbm).
destruct (dup_blk_facts ly S W mem md b m HAR Hbm) as (HbyS & _).
destruct (dup_blk_facts ly1 S1 W1 mem1 md1 b m HAR1 Hin1) as (HbyS1 & _).
split; [exact (proj2 (HbyS a Hin))|].
split; [exact (proj2 (HbyS1 a Hin))|].
intros Hblk.
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2
(al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 b m HAR1 Hin1))))))) as Hpw.
assert (Hdis : zdisjoint (b, req_size m) (dst, req_size n)).
{ apply (pairwise_In zdisjoint (map (fun q => (fst q, req_size (snd q))) (ablocks B ly1 S1))
(b, req_size m) (dst, req_size n)
(map (fun q => (fst q, req_size (snd q))) (ablocks B ly S))
(map (fun q => (fst q, req_size (snd q))) [(dst, n)])).
- rewrite HBL, map_app. reflexivity.
- exact Hpw.
- exact (in_map (fun q => (fst q, req_size (snd q))) _ (b, m) Hbm).
- left. reflexivity. }
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. lia.
Qed.

End c.
End b.
