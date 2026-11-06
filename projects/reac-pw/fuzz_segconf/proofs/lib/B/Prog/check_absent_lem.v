(* the image-B port of lib/A/Prog/check_absent_lem.v (commit 5ed426e78b84): the helper
   lemmas of the image-B walk lib/B/Prog/check_absent.v (fuzz_segconf.asan-ubsan). The text is the image-A file's;
   only the Require lines change: the kit modules copied for image B (YA0n YG0f YG0n YG0s YG0d YCbq) and the contract
   base (SegPgBase SegABase reac_segconf_find_c) come from lib.B, the other kit modules stay lib.Reusable. No lemma
   here names an image number: the window bounds and alloc_ceiling are parameters or kit constants. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase reac_segconf_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* absent: no entry has the name, so every accessor the four calls compute answers None / false *)
Lemma ca_absent_none : forall rcs nm, absent rcs nm = true ->
  r_find rcs nm = None /\ r_role rcs nm = None /\ r_ignored rcs nm = false /\ r_model rcs nm = None.
Proof.
  intros rcs nm H. unfold absent in H.
  destruct (r_find rcs nm); [discriminate|].
  destruct (r_role rcs nm); [discriminate|].
  destruct (r_ignored rcs nm); [discriminate|].
  destruct (r_model rcs nm); [discriminate|].
  repeat split.
Qed.

(* a reader that agrees with another one outside the window [lo, hi), on the addresses a program object can have *)
Definition ca_kept (rd rd' : reader) (lo hi : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma ca_kept_refl : forall rd lo hi, ca_kept rd rd lo hi.
Proof. intros rd lo hi a _ _. reflexivity. Qed.
Lemma ca_kept_trans : forall rd rd1 rd2 lo hi, ca_kept rd rd1 lo hi -> ca_kept rd1 rd2 lo hi -> ca_kept rd rd2 lo hi.
Proof. intros rd rd1 rd2 lo hi H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.
Lemma ca_kept_sub : forall rd rd' lo hi lo' hi', ca_kept rd rd' lo' hi' -> lo <= lo' -> hi' <= hi -> ca_kept rd rd' lo hi.
Proof. intros rd rd' lo hi lo' hi' H H1 H2 a Ha Hn. apply H; [exact Ha | lia]. Qed.

Section cc. Context {rc : YM05.RunCeil}.
(* the shadow byte of an address below alloc_ceiling, and the shadow words of a range's hull, lie below
   alloc_ceiling and above 4096 (SHADOW_OFF = 0x7fff8000, alloc_ceiling >= CEIL_MIN = 0x7fff7f800000) *)
Lemma ca_shadow_low : forall x, 0 <= x -> x < alloc_ceiling -> 4096 <= SHADOW_OFF + x / 8 < alloc_ceiling.
Proof using.
  intros x H0 H. pose proof alloc_ceiling_value as [[Hmin Hmax] _].
  assert (Hd : x / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
  assert (HC : 140737479966720 / 8 = 17592184995840) by reflexivity.
  assert (H0d : 0 <= x / 8) by (apply Z.div_pos; lia).
  unfold SHADOW_OFF. lia.
Qed.
Lemma ca_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= alloc_ceiling ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 4096 <= s < alloc_ceiling.
Proof using.
  intros x n s H0 Hn Hxn Hs. pose proof alloc_ceiling_value as [[Hmin Hmax] _].
  unfold shadow_addr in Hs.
  assert (L1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (L2 : 268431360 <= (SHADOW_OFF + x / 8) / 8).
  { apply Z.div_le_lower_bound; [lia|]. unfold SHADOW_OFF. lia. }
  assert (U1 : (x + n - 1) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
  assert (UC : 140737479966720 / 8 = 17592184995840) by reflexivity.
  assert (U2 : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (x + n - 1) / 8).
  { rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
  unfold SHADOW_OFF in *. lia.
Qed.
(* the word-at-a-time slack after a terminator below alloc_ceiling stays below it: alloc_ceiling is a multiple
   of 4096, so of 8 *)
Lemma ca_tail_low : forall e, 0 <= e -> e < alloc_ceiling -> e - e mod 8 + 8 <= alloc_ceiling.
Proof using.
  intros e H0 He. pose proof alloc_ceiling_value as [_ CMOD].
  assert (H8 : alloc_ceiling mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact CMOD]]. }
  apply Z.mod_divide in H8 as [q Hq]; [|lia].
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hb.
  pose proof (Z.div_mod e 8 ltac:(lia)) as Hdm.
  assert (Hlt : e / 8 < q) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* everything in [4096, alloc_ceiling) is outside a window that starts at or above alloc_ceiling *)
Lemma ca_kept_low : forall rd rd' lo hi, ca_kept rd rd' lo hi -> alloc_ceiling <= lo ->
  forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.
Proof using.
  intros rd rd' lo hi H Hlo a Ha. pose proof alloc_ceiling_value as [[Hmin Hmax] _].
  apply H; lia.
Qed.
(* the shadow fact of a range below alloc_ceiling survives such an agreement *)
Lemma ca_addr_low : forall (rd rd' : reader) q n, (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) ->
  0 <= q -> q + n <= alloc_ceiling -> sa_addr rd q n -> sa_addr rd' q n.
Proof using.
  intros rd rd' q n L Hq Hqn (A1 & A2 & A3 & A4 & A5).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
  - intros x Hx. destruct (A4 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite L; [exact Hs|]. unfold shadow_of_addr. pose proof (ca_shadow_low x ltac:(lia) ltac:(lia)). lia.
  - intros Hn s Hs. rewrite L; [exact (A5 Hn s Hs)|].
    pose proof (ca_hull_low q n s Hq Hn Hqn Hs). lia.
Qed.
End cc.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* where a query's objects lie: in [4096, alloc_ceiling) (blocks and frames by AR's laws, image bytes by the
   image's own bound) *)
Lemma ca_loc_low : forall ly S W mem md q n,
  AR segs B ly S W mem md -> (forall a, in_img segs a -> 4096 <= a < alloc_ceiling) ->
  sa_loc segs B ly S q n -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof using LAWS.
  intros ly S W mem md q n HAR HI HL Hn.
  destruct HL as [(b & m & Hb & H1 & H2) | [(cid & pos & Hf & _ & H1 & H2) | HM]].
  - destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & H4 & Hc & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
  - destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ HF].
    pose proof (proj1 (Forall_forall _ _) HF (cid, pos) Hf) as Hfb. cbn [fst snd] in Hfb. lia.
  - destruct (HM q ltac:(lia)) as (Hq & _ & _). destruct (HM (q + n - 1) ltac:(lia)) as (Hq' & _ & _).
    pose proof (HI _ Hq). pose proof (HI _ Hq'). lia.
Qed.

(* the callees' query premise at a later state whose reader agrees with the entry's on [4096, alloc_ceiling),
   whose blocks are a permutation of the entry's and whose frames include the entry's, at the same layout *)
Lemma ca_qp_kept : forall ly S ly' S' (rd rd' : reader) c name rcs nm,
  (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) ->
  Permutation (ablocks B ly' S') (ablocks B ly S) -> ly' = ly ->
  (forall f, In f (frames S) -> In f (frames S')) ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= alloc_ceiling ->
  4096 <= name -> name + (Z.of_nat (length nm) + 1) <= alloc_ceiling ->
  query_pre segs B ly S rd c name rcs nm -> query_pre segs B ly' S' rd' c name rcs nm.
Proof using.
  intros ly S ly' S' rd rd' c name rcs nm L HP Hly HF Hc0 Hc Hn0' Hn QP. subst ly'.
  pose proof alloc_ceiling_value as [[Hmin Hmax] Hmod].
  destruct QP as (Hc0' & Hc16 & (bs & Hbs & Henc) & (b & m & Hbm & Hb1 & Hb2) & HAc & Hn0 & (Hsz & Htl) & Hloc
    & HAn & Hlen).
  unfold query_pre.
  refine (conj Hc0' (conj Hc16 (conj _ (conj _ (conj _ (conj Hn0 (conj _ (conj _ (conj _ Hlen))))))))).
  - exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
    rewrite L; [exact (Hbs i Hi)|]. unfold seg_spec.SEG_C_SIZE in Hc, Hl. lia.
  - exists b, m. split; [eapply Permutation_in; [symmetry; exact HP | exact Hbm] | lia].
  - exact (ca_addr_low rd rd' c seg_spec.SEG_C_SIZE L ltac:(lia) Hc HAc).
  - split.
    + destruct Hsz as [Hz Hnz]. split; [|exact Hnz]. intros i Hi.
      rewrite length_app in Hi. cbn [length] in Hi.
      rewrite L; [exact (Hz i ltac:(rewrite length_app; cbn [length]; lia))|]. lia.
    + intros x Hx.
      assert (HTL : name + Z.of_nat (length nm) - (name + Z.of_nat (length nm)) mod 8 + 8 <= alloc_ceiling)
        by (apply ca_tail_low; lia).
      rewrite L; [exact (Htl x Hx)|]. lia.
  - destruct Hloc as [(b2 & m2 & Hb & H1 & H2) | [(cid & pos & Hf & H0 & H1 & H2) | HM]].
    + left. exists b2, m2. split; [eapply Permutation_in; [symmetry; exact HP | exact Hb] | lia].
    + right; left. exists cid, pos. split; [apply HF; exact Hf|]. split; [exact H0 | lia].
    + right; right. exact HM.
  - exact (ca_addr_low rd rd' name (Z.of_nat (length nm) + 1) L ltac:(lia) Hn HAn).
Qed.

(* arodata_okP at a later state: every read-only byte lies below the window *)
Lemma ca_rodata_kept : forall RLO RHI (rd rd' : reader) lo hi,
  ca_kept rd rd' lo hi ->
  (forall a, in_roP segs RLO RHI a -> 0 <= a < 2 ^ 64 /\ a < lo) ->
  arodata_okP segs RLO RHI B rd -> arodata_okP segs RLO RHI B rd'.
Proof using.
  intros RLO RHI rd rd' lo hi HK HB0 HR a Hro Ho He.
  destruct (HB0 a Hro) as [Hb Hlt]. rewrite (HK a Hb ltac:(lia)). exact (HR a Hro Ho He).
Qed.
End e.

(* the callees' post tails compose *)
Lemma ca_noalloc_trans : forall B ly S ly1 S1 ly2 S2,
  sa_noalloc B ly S ly1 S1 -> sa_noalloc B ly1 S1 ly2 S2 -> sa_noalloc B ly S ly2 S2.
Proof using.
  intros B ly S ly1 S1 ly2 S2 (P1 & -> & f1 & ->) (P2 & -> & f2 & ->).
  split; [exact (Permutation_trans P2 P1)|]. split; [reflexivity|]. exists f2. reflexivity.
Qed.
End d.
