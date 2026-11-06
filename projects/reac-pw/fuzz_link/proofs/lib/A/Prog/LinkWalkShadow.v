(* reac-pw/fuzz_link, image A: carrying `range_addressable` / `shadow_hull_vis` of a caller's buffer across a step
   (a callee's apost, or a run of the walk's own code), by the class of each byte.

   A callee's apost keeps a byte's SHADOW only for its heap blocks' granules (ashadow_kept) and for the side frames of the call (akept's
   frame clause). link-a/form/FORM.md (internal record, sha256 13aeff774164) section 3a: the other classes are pinned by AR at both ends. So:
   - the real stack [ly_stk_lo, ly_stk_hi): the first row of zero_shadow_ranges (YG0n.v), zero at every AR state;
   - a heap block still alive after the step: AR_shadow_law (YG0d.v: block_shadow and the hull of the block);
   - the image [0x10000, pcap_img_end): every image granule's shadow byte lies in a row of Tfib_zero_shadow or is a
     constant shadow cell of Tfib_const_shadow (checked by computation below, `img_sweep`), so it is the same at
     every AR state of a `PcapSyms B` (AF0m.v ts_zsh, ts_const);
   - a side frame of the call: akept's frame clause keeps the frame's shadow (frames are 64-aligned and a multiple
     of 64 bytes, YG0s.v frame_facts, so a byte's 8-byte shadow group lies inside its frame's shadow).
   NOT pinned (and so not a class here): an address above alloc_ceiling outside the stack row, i.e.
   [alloc_ceiling, ly_stk_lo) and [ly_stk_hi, kHighMemEnd): AR's ahz stops at ASAN_CEIL = alloc_ceiling and
   zero_shadow_ranges has only the stack row there.

   Per byte x: `saddr rd x` (its shadow byte usable for x) and `gvis rd x` (its 8-byte shadow group visible);
   `range_addressable` is saddr on every byte and `shadow_hull_vis` is gvis on every byte (hull_of_gvis /
   gvis_of_hull). `sbyte_transport` carries both across a step with akept from the first state; the range form is
   `shadow_transport`; its premise on the step's exception set E is only `fmiss` (E misses the shadow of the frames
   of Sc), which `fmiss_app` (an application-byte write set), `fmiss_side` (a side frame the walk took, LinkWalkSide.v
   aside_rng) and `fmiss_or` give. `sclass_of_ajw` places a byte a caller may write (apre's ajw: window, block, own
   frame, G, out cell); `sclass_of_akb` a byte of a read set (link_amem.v's narrowed akb, clause 1 the stack row);
   `shadow_transport_akb` is the transport of a read-set range.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0q YF0v YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkZsh LinkWalkSide.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the image's shadow is covered by the tables ----
   A sweep over the image's shadow [SHADOW_OFF + 0x2000, SHADOW_OFF + 0xca800): at each point either a row of
   Tfib_zero_shadow holds it (jump to the row's end) or the next constant shadow cell of Tfib_const_shadow (a list
   sorted by address, consumed in order) is a one-byte cell at that point (step by one). 31 rows and 9151 cells, so
   the computation is linear. *)
Definition row_hit (s : Z) (r : Z * Z) : bool :=
  (SHADOW_OFF + fst r / 8 <=? s) && (s <? SHADOW_OFF + fst r / 8 + snd r / 8).
Definition row_end (r : Z * Z) : Z := SHADOW_OFF + fst r / 8 + snd r / 8.
Definition cell_ok (s : Z) (c : acell) : bool :=
  match c with ACell (ANum a) w (AV (ANum _)) => (a =? s) && Nat.ltb 0 w | _ => false end.
Definition cell_lt (s : Z) (c : acell) : bool :=
  match c with ACell (ANum a) _ _ => a <? s | _ => true end.
Fixpoint drop_below (s : Z) (cl : list acell) : list acell :=
  match cl with c :: t => if cell_lt s c then drop_below s t else cl | [] => [] end.
Fixpoint sweep (fuel : nat) (cur hi : Z) (cl : list acell) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? cur then true else
      match find (row_hit cur) Tfib_zero_shadow with
      | Some r => sweep f (row_end r) hi cl
      | None => match drop_below cur cl with
                | c :: cl' => if cell_ok cur c then sweep f (cur + 1) hi cl' else false
                | [] => false
                end
      end
  end.

Lemma drop_below_in : forall s cl c, In c (drop_below s cl) -> In c cl.
Proof.
  intros s cl. induction cl as [|h t IH]; intros c Hc; cbn [drop_below] in Hc; [exact Hc|].
  destruct (cell_lt s h); [right; exact (IH c Hc) | exact Hc].
Qed.

Lemma sweep_sound : forall fuel cur hi cl, sweep fuel cur hi cl = true ->
  (forall c, In c cl -> In c Tfib_const_shadow) ->
  forall s, cur <= s < hi ->
  (exists r, In r Tfib_zero_shadow /\ row_hit s r = true) \/ (exists c, In c Tfib_const_shadow /\ cell_ok s c = true).
Proof.
  induction fuel as [|f IH]; intros cur hi cl H Hcl s Hs; cbn [sweep] in H; [discriminate|].
  destruct (Z.leb_spec hi cur) as [Hh|Hh]; [lia|].
  destruct (find (row_hit cur) Tfib_zero_shadow) as [r|] eqn:Hf.
  - destruct (find_some _ _ Hf) as [Hin Hr].
    destruct (Z_lt_le_dec s (row_end r)) as [Hlt|Hge].
    + left. exists r. split; [exact Hin|]. unfold row_hit, row_end in *.
      apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    + exact (IH (row_end r) hi cl H Hcl s ltac:(lia)).
  - destruct (drop_below cur cl) as [|c cl'] eqn:Hd; [discriminate|].
    destruct (cell_ok cur c) eqn:Hc; [|discriminate].
    assert (Hinc : In c Tfib_const_shadow) by (apply Hcl; apply (drop_below_in cur cl c); rewrite Hd; left; reflexivity).
    destruct (Z.eq_dec s cur) as [-> | Hne].
    + right. exists c. split; [exact Hinc | exact Hc].
    + refine (IH (cur + 1) hi cl' H _ s ltac:(lia)).
      intros c' Hc'. apply Hcl. apply (drop_below_in cur cl c'). rewrite Hd. right. exact Hc'.
Qed.

Lemma img_end_val : pcap_img_end = 0x654000.
Proof. reflexivity. Qed.

Lemma img_sweep : sweep 20000 (SHADOW_OFF + 0x2000) (SHADOW_OFF + 0xca800) Tfib_const_shadow = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- bytes and their shadow groups ---- *)
Definition saddr (rd : reader) (x : Z) : Prop :=
  exists s, rd (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s.
Definition gvis (rd : reader) (x : Z) : Prop :=
  forall s, shadow_addr x / 8 * 8 <= s < shadow_addr x / 8 * 8 + 8 -> rd s <> None.

Lemma saddr_of_ra : forall rd p n x, range_addressable rd SHADOW_OFF p n -> p <= x < p + n -> saddr rd x.
Proof. intros rd p n x H Hx. exact (H x Hx). Qed.

Lemma ra_of_saddr : forall rd p n, (forall x, p <= x < p + n -> saddr rd x) -> range_addressable rd SHADOW_OFF p n.
Proof. intros rd p n H x Hx. exact (H x Hx). Qed.

Lemma gvis_of_hull : forall rd p n x, shadow_hull_vis rd p n -> p <= x < p + n -> gvis rd x.
Proof.
  intros rd p n x H Hx s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

Lemma hull_of_gvis : forall rd p n, 0 < n -> (forall x, p <= x < p + n -> gvis rd x) -> shadow_hull_vis rd p n.
Proof.
  intros rd p n Hn H s Hs.
  (* the byte of [p, p + n) whose shadow group holds s *)
  set (g := (s / 8) * 64 - SHADOW_OFF * 8).
  assert (Hx : p <= Z.max p g < p + n) by (unfold g, shadow_addr, SHADOW_OFF in *; lia).
  apply (H (Z.max p g) Hx). unfold g, shadow_addr, SHADOW_OFF in *. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit argument, as in link_amem.v and LinkWalkSide.v. *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis TB : PcapSyms B.
Hypothesis segs_img : forall a, in_img segs a -> 0x10000 <= a < pcap_img_end.

(* every image shadow byte has the same value at every AR state, and is visible *)
Lemma img_sh_eq : forall ly1 S1 rd1 ly2 S2 rd2 s, ARm B ly1 S1 rd1 -> ARm B ly2 S2 rd2 ->
  SHADOW_OFF + 0x2000 <= s < SHADOW_OFF + 0xca800 -> rd2 s = rd1 s /\ rd1 s <> None.
Proof.
  intros ly1 S1 rd1 ly2 S2 rd2 s M1 M2 Hs.
  destruct (sweep_sound _ _ _ _ img_sweep (fun c Hc => Hc) s Hs) as [(r & Hin & Hb) | (c & Hin & Hok)].
  - destruct r as [lo n]. unfold row_hit in Hb. cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    pose proof (zsh_row_zero B TB ly1 S1 rd1 lo n M1 Hin) as Z1.
    pose proof (zsh_row_zero B TB ly2 S2 rd2 lo n M2 Hin) as Z2.
    unfold zero_shadow, shadow_of_addr in Z1, Z2.
    replace s with (SHADOW_OFF + lo / 8 + (s - (SHADOW_OFF + lo / 8))) by lia.
    rewrite (Z1 (s - (SHADOW_OFF + lo / 8)) ltac:(lia)), (Z2 (s - (SHADOW_OFF + lo / 8)) ltac:(lia)).
    split; [reflexivity | discriminate].
  - destruct c as [ca w cv]. unfold cell_ok in Hok.
    destruct ca; try discriminate. destruct cv as [e|]; [|discriminate]. destruct e; try discriminate.
    apply andb_prop in Hok as [Ha Hw]. apply Z.eqb_eq in Ha. apply Nat.ltb_lt in Hw. subst z.
    assert (HinT : forall ly, In (ACell (ANum s) w (AV (ANum z0))) (as_const B ly)).
    { intros ly. rewrite (ts_const B TB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    pose proof (proj1 (Forall_forall _ _) (am_const B ly1 S1 rd1 M1) _ (HinT ly1)) as C1.
    pose proof (proj1 (Forall_forall _ _) (am_const B ly2 S2 rd2 M2) _ (HinT ly2)) as C2.
    unfold cell_holds in C1, C2. cbn [c_at c_w c_val aeval] in C1, C2.
    specialize (C1 0%nat Hw). specialize (C2 0%nat Hw). rewrite Z.add_0_r in C1, C2.
    rewrite C1, C2. split; [reflexivity | discriminate].
Qed.

(* the four classes AR pins *)
Definition sclass (ly : alayout) (S : astate) (x : Z) : Prop :=
  (ly_stk_lo ly <= x < ly_stk_hi ly)
  \/ (exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m)
  \/ in_img segs x
  \/ (exists c q, In (c, q) (frames S) /\ frame_addr ly c q <= x < frame_addr ly c q + fs_frame_bytes c).

(* what a step's exception set E must miss for the side-frame case: the shadow of the frames of Sc (akept's frame
   clause keeps a frame's shadow byte only where E misses it). Nothing else of E matters: the stack row, the heap
   blocks and the image are pinned by AR at the later state. *)
Definition fmiss (lyc : alayout) (Sc : astate) (E : Z -> Prop) : Prop :=
  forall c q s, In (c, q) (frames Sc) ->
    shadow_addr (frame_addr lyc c q) <= s < shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8 -> ~ E s.

Lemma fmiss_or : forall lyc Sc (E1 E2 : Z -> Prop), fmiss lyc Sc E1 -> fmiss lyc Sc E2 ->
  fmiss lyc Sc (fun a => E1 a \/ E2 a).
Proof. intros lyc Sc E1 E2 H1 H2 c q s Hin Hs [H|H]; [exact (H1 c q s Hin Hs H) | exact (H2 c q s Hin Hs H)]. Qed.

Lemma fmiss_mono : forall lyc Sc (E1 E2 : Z -> Prop), fmiss lyc Sc E1 -> (forall a, E2 a -> E1 a) -> fmiss lyc Sc E2.
Proof. intros lyc Sc E1 E2 H1 Hi c q s Hin Hs H. exact (H1 c q s Hin Hs (Hi s H)). Qed.

(* an exception set of application bytes (a callee's write set) misses every frame's shadow *)
Lemma fmiss_app : forall lyc Sc (W : world segs) memc mdc (E : Z -> Prop), AR segs B lyc Sc W memc mdc ->
  (forall a, E a -> a < kLowMemEnd \/ kHighMemBeg <= a) -> fmiss lyc Sc E.
Proof.
  intros lyc Sc W memc mdc E HAR HE c q s Hin Hs HEs.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c q HAR Hin) as (Hf4096 & Hfceil & _).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (HE s HEs) as [H|H]; unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *; lia.
Qed.

(* a side frame the walk took, which is not a frame of Sc (its range, its shadow, its flag byte: LinkWalkSide.v's
   aside_rng), misses the shadow of every frame of Sc *)
Lemma fmiss_side : forall lyc Sc (W : world segs) memc mdc cid pos,
  AR segs B lyc Sc W memc mdc -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames Sc) ->
  fmiss lyc Sc (aside_rng lyc cid pos).
Proof.
  intros lyc Sc W memc mdc cid pos HAR Hc Hp NIN c q s Hin Hs HE.
  pose proof HAR as (M & _).
  destruct (frame_facts B lyc Sc _ c q M Hin) as (C1 & C2 & FA & _ & PF & P1 & P2 & P3 & P4 & P5 & _).
  unfold page_aligned in PF.
  pose proof (frame_off_bounds cid pos Hc Hp) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (flag_off_bounds cid pos Hc Hp) as AF.
  pose proof (Z.mul_nonneg_nonneg c (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
  pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
  pose proof FA as [F1 F2].
  assert (FINcq : in_app (frame_addr lyc c q) (fs_frame_bytes c)).
  { apply (in_app_sub (ly_F lyc) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia. }
  destruct HE as [Hr | [Hr | Hr]].
  - (* a byte of the taken frame: application memory, not a shadow byte *)
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    refine (app_vs_shadow (ly_F lyc) kFakeStackSize (frame_addr lyc c q) (fs_frame_bytes c) s FA FINcq ltac:(lia) _ Hs).
    unfold frame_addr, kFakeFramesOff in *. lia.
  - (* the taken frame's shadow: disjoint from (c, q)'s, as the frames are *)
    unfold in_zr in Hr. cbn [fst snd] in Hr.
    assert (NE : (c, q) <> (cid, pos)) by (intros E; rewrite E in Hin; exact (NIN Hin)).
    pose proof (frames_apart c q cid pos C1 C2 Hc Hp NE) as D.
    assert (FA8 : forall c' q', fs_frame_off c' q' mod 64 = 0 -> frame_addr lyc c' q' mod 8 = 0).
    { intros c' q' H. unfold frame_addr. apply Z.mod_divide; [lia|]. apply Z.mod_divide in PF as [k Hk]; [|lia].
      apply Z.mod_divide in H as [k' Hk']; [|lia]. exists (k * 512 + k' * 8). lia. }
    assert (D' : zdisjoint (frame_addr lyc c q, fs_frame_bytes c) (frame_addr lyc cid pos, fs_frame_bytes cid)).
    { unfold zdisjoint, frame_addr in *. cbn [fst snd] in *. lia. }
    pose proof (shadow_apart (frame_addr lyc c q) (fs_frame_bytes c) (frame_addr lyc cid pos) (fs_frame_bytes cid)
      ltac:(unfold frame_addr, kFakeFramesOff in *; lia) ltac:(unfold frame_addr, kFakeFramesOff in *; lia)
      (FA8 c q P3) (FA8 cid pos A3)
      ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in P5 as [k Hk]; [|lia]; exists (k * 8); lia)
      ltac:(apply Z.mod_divide; [lia|]; pose proof A5 as A5'; apply Z.mod_divide in A5' as [k Hk]; [|lia]; exists (k * 8); lia)
      ltac:(lia) ltac:(lia) D') as SD.
    unfold zdisjoint in SD. cbn [fst snd] in SD. lia.
  - (* the taken frame's flag byte: application memory in the side stack's flag area *)
    subst s.
    refine (app_vs_shadow (ly_F lyc) kFakeStackSize (frame_addr lyc c q) (fs_frame_bytes c) (flag_addr lyc cid pos)
      FA FINcq ltac:(lia) _ Hs).
    unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.

Lemma sbyte_transport : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi
    (E : Z -> Prop) x,
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E -> fmiss lyc Sc E ->
  sclass lyc Sc x ->
  saddr (aview segs (w_H W) memc) x -> gvis (aview segs (w_H W) memc) x ->
  saddr (aview segs (w_H W2) mem2) x /\ gvis (aview segs (w_H W2) mem2) x.
Proof.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E x HAR1 HAR2 Elo Ehi Hbl HK HE Hc Hs1 Hg1.
  pose proof HAR1 as (M1 & _). pose proof HAR2 as (M2 & _).
  destruct Hc as [Hst | [(b & m & Hin & Hb) | [Hi | (c & q & Hin & Hf)]]].
  - (* the real stack: zero at every AR state *)
    pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly2 S2 _ M2) (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2)
      ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
    pose proof (am_layout B ly2 S2 _ M2) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
    unfold page_aligned in Pl, Ph. rewrite Elo, Ehi in *.
    split.
    + exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
      replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
      apply HZ. lia.
    + intros s Hs.
      replace s with (SHADOW_OFF + ly_stk_lo lyc / 8 + (s - (SHADOW_OFF + ly_stk_lo lyc / 8))) by lia.
      rewrite HZ; [discriminate|]. unfold shadow_addr, SHADOW_OFF in *. lia.
  - (* a heap block still alive *)
    pose proof (Hbl b m Hin) as Hin2.
    destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as [HBS _].
    split.
    + exact (block_shadow_range _ _ _ _ x 1 HBS ltac:(lia) ltac:(lia) x ltac:(lia)).
    + intros s Hs.
      apply (shadow_hull_vis_of_block segs B LAWS ly2 S2 W2 mem2 md2 b m x 1 HAR2 Hin2 ltac:(lia) ltac:(lia) ltac:(lia)).
      replace (x + 1 - 1) with x by lia. exact Hs.
  - (* the image *)
    pose proof (segs_img x Hi) as Hi'. rewrite img_end_val in Hi'.
    assert (Hsx : SHADOW_OFF + 0x2000 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 0xca800)
      by (unfold shadow_of_addr; lia).
    destruct (img_sh_eq lyc Sc _ ly2 S2 _ _ M1 M2 Hsx) as [Eq _].
    split.
    + destruct Hs1 as (v & Hv & Hok). exists v. rewrite Eq. split; [exact Hv | exact Hok].
    + intros s Hs.
      destruct (img_sh_eq lyc Sc _ ly2 S2 _ s M1 M2 ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)) as [Eq2 Hn].
      rewrite Eq2. exact Hn.
  - (* a side frame of the call *)
    pose proof HK as (_ & _ & _ & K4 & _).
    destruct (frame_facts B lyc Sc _ c q M1 Hin) as (_ & _ & Happ & _ & PF & _ & _ & Hoff & H64 & Hb64 & _).
    unfold page_aligned in PF. unfold in_app, kFakeStackSize in Happ.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c q HAR1 Hin) as (Hf4096 & Hfceil & _).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    assert (HF64 : frame_addr lyc c q mod 64 = 0) by (unfold frame_addr; lia).
    assert (KS : forall s, shadow_addr x / 8 * 8 <= s < shadow_addr x / 8 * 8 + 8 ->
      aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
    { intros s Hs.
      assert (Hsf : shadow_addr (frame_addr lyc c q) <= s < shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8)
        by (unfold shadow_addr, SHADOW_OFF in *; lia).
      apply (K4 c q s Hin).
      - right. unfold in_zr. cbn [fst snd]. exact Hsf.
      - exact (HE c q s Hin Hsf). }
    split.
    + destruct Hs1 as (v & Hv & Hok). exists v. split; [|exact Hok].
      rewrite (KS (shadow_of_addr SHADOW_OFF x)); [exact Hv|]. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
    + intros s Hs. rewrite (KS s Hs). exact (Hg1 s Hs).
Qed.

Lemma shadow_transport : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi
    (E : Z -> Prop) p n,
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E -> fmiss lyc Sc E ->
  0 < n -> (forall x, p <= x < p + n -> sclass lyc Sc x) ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF p n -> shadow_hull_vis (aview segs (w_H W) memc) p n ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF p n /\ shadow_hull_vis (aview segs (w_H W2) mem2) p n.
Proof.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E p n HAR1 HAR2 Elo Ehi Hbl HK HE Hn Hc HR HH.
  assert (T : forall x, p <= x < p + n ->
    saddr (aview segs (w_H W2) mem2) x /\ gvis (aview segs (w_H W2) mem2) x).
  { intros x Hx. apply (sbyte_transport lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E x HAR1 HAR2 Elo Ehi Hbl HK HE
      (Hc x Hx) (saddr_of_ra _ p n x HR Hx) (gvis_of_hull _ p n x HH Hx)). }
  split.
  - apply ra_of_saddr. intros x Hx. exact (proj1 (T x Hx)).
  - apply hull_of_gvis; [exact Hn|]. intros x Hx. exact (proj2 (T x Hx)).
Qed.

(* the class of a byte a caller may write (apre's ajw), when it is an application byte *)
Lemma sclass_of_ajw : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (a < kLowMemEnd \/ kHighMemBeg <= a) ->
  sclass lyc Sc a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HG HJ Hw Happ.
  destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + left. rewrite Elo, Ehi. lia.
    + right; left. exists b, n. split; [exact Hin | exact Hr].
    + right; left. exists b, n. split; [exact Hin | exact Hr].
    + assert (Hcq : In (c, q) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
      destruct Hr as [Hr | Hr].
      * right; right; right. exists c, q. split; [exact Hcq|]. unfold in_zr in Hr. cbn [fst snd] in Hr. exact Hr.
      * exfalso. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hf4096 & Hfceil & _).
        pose proof (fs_frame_bytes_nonneg c) as Hnn. pose proof asan_consts as ((C1a & C1b) & _).
        unfold in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. lia.
  - right; right; left. destruct (HG a HGa) as (Hi & _). exact Hi.
  - left. rewrite Elo, Ehi. lia.
Qed.

(* the class of a byte of a read set (`akb`, link_amem.v 7cd4e1d95689: clause 1 is the real-stack row) *)
Lemma sclass_of_akb : forall lyc Sc slo shi a,
  akb segs B lyc Sc slo shi a -> sclass lyc Sc a.
Proof.
  intros lyc Sc slo shi a Hb.
  destruct Hb as [(H1 & _) | [(b & m & Hin & Hr) | [(Hi & _) | (c & q & Hin & Hr)]]].
  - left. exact H1.
  - right; left. exists b, m. split; [exact Hin | exact Hr].
  - right; right; left. exact Hi.
  - right; right; right. exists c, q. split; [exact Hin|]. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact Hr.
Qed.

(* a read-set range's shadow facts, from the call state to any later AR state the step's akept reaches *)
Lemma shadow_transport_akb : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi
    (E : Z -> Prop) p n,
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E -> fmiss lyc Sc E ->
  0 < n -> (forall a, p <= a < p + n -> akb segs B lyc Sc slo shi a) ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF p n -> shadow_hull_vis (aview segs (w_H W) memc) p n ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF p n /\ shadow_hull_vis (aview segs (w_H W2) mem2) p n.
Proof.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E p n HAR1 HAR2 Elo Ehi Hbl HK HE Hn Hb.
  apply (shadow_transport lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E p n HAR1 HAR2 Elo Ehi Hbl HK HE Hn).
  intros x Hx. exact (sclass_of_akb lyc Sc slo shi x (Hb x Hx)).
Qed.

(* A byte of one of the four classes AR pins at the call (`sclass`: a read-set byte by `sclass_of_akb`, a byte of
   the caller's write set by `sclass_of_ajw`) is not a byte of a side frame that is free at the call: not in its
   range, not in its shadow, not its flag byte (LinkWalkSide.v aside_rng). So the walk's own frame, taken after the
   call, never meets them, and an akept whose exception set is `E \/ aside_rng` keeps every such byte outside E. *)
Lemma sclass_not_side : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k cid pos a,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames Sc) ->
  sclass lyc Sc a -> ~ aside_rng lyc cid pos a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k cid pos a HJ Hc Hp NIN Hb HS.
  assert (HR := HJ). apply ajournal_gx_row in HR. destruct HR as (R1 & R2 & R3 & R4).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  pose proof HAR as (M & LG & _).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F lyc, kFakeStackSize)
    ltac:(unfold owned_extents; cbn; tauto)) as FA. cbn [fst snd] in FA.
  pose proof FA as [F1 F2].
  pose proof (frame_off_bounds cid pos Hc Hp) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (flag_off_bounds cid pos Hc Hp) as AF.
  pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof ASAN_CEIL_range as [CR _].
  assert (FIN : in_app (frame_addr lyc cid pos) (fs_frame_bytes cid)).
  { apply (in_app_sub (ly_F lyc) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia. }
  (* the parts of aside_rng in the side stack's region, and its shadow part *)
  assert (HF : forall x, (in_zr x (frame_rng lyc (cid, pos)) \/ x = flag_addr lyc cid pos) ->
    in_zr x (ly_F lyc, kFakeStackSize)).
  { intros x [Hx | ->].
    - unfold in_zr, frame_rng, frame_addr in *. cbn [fst snd] in *. unfold kFakeFramesOff in *. lia.
    - unfold in_zr, flag_addr, kFakeFlagsOff, kFakeFramesOff in *. cbn [fst snd]. lia. }
  assert (HF' : forall x, in_zr x (ly_F lyc, kFakeStackSize) -> ~ (ly_stk_lo lyc <= x < ly_stk_hi lyc) /\
    ~ in_zr x (ly_img lyc)).
  { intros x Hx. destruct (owned_extents_bound lyc x LO ltac:(apply Exists_exists;
      exists (ly_F lyc, kFakeStackSize); split; [unfold owned_extents; cbn; tauto | exact Hx])) as (_ & NS & NI).
    split; [exact NS | exact NI]. }
  assert (HSH : in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
    kLowMemEnd <= a < kHighMemBeg).
  { intros Hs. unfold in_zr in Hs. cbn [fst snd] in Hs. unfold in_app, kLowShadowBeg in FIN.
    unfold shadow_addr, frame_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
  destruct Hb as [Hst | [(b & m & Hin & Hr) | [Hi | (c & q & Hin & Hr)]]].
  - (* the stack row *)
    destruct HS as [Hs | [Hs | Hs]].
    + exact (proj1 (HF' a (HF a (or_introl Hs))) Hst).
    + pose proof (HSH Hs). lia.
    + exact (proj1 (HF' a (HF a (or_intror Hs))) Hst).
  - (* a heap block of Sc *)
    apply In_ablocks in Hin as (kc & Hk & Hstt & Hu & Hn).
    pose proof (chunk_facts B lyc Sc _ kc M Hk) as (G1 & G2 & _ & G4 & _).
    assert (HX : ck_base B lyc kc <= a < ck_base B lyc kc + ck_extent kc).
    { apply (user_in_extent B lyc Sc _ kc a M Hk). rewrite <- G4, Hu, Hn. exact Hr. }
    pose proof (chunk_vs_F B lyc Sc _ kc M Hk) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    destruct HS as [Hs | [Hs | Hs]].
    + pose proof (HF a (or_introl Hs)) as Hx. unfold in_zr in Hx. cbn [fst snd] in Hx. lia.
    + refine (app_vs_shadow (ck_base B lyc kc) (ck_extent kc) (frame_addr lyc cid pos) (fs_frame_bytes cid) a
        G1 FIN ltac:(lia) HX _). unfold in_zr in Hs. cbn [fst snd] in Hs. exact Hs.
    + pose proof (HF a (or_intror Hs)) as Hx. unfold in_zr in Hx. cbn [fst snd] in Hx. lia.
  - (* an image byte *)
    assert (HI : in_zr a (ly_img lyc)).
    { destruct Hi as (sg & Hsg & Hr). pose proof (al_img _ _ _ _ LG sg Hsg). unfold in_zr. lia. }
    pose proof (segs_img a Hi) as Hlow. rewrite img_end_val in Hlow.
    destruct HS as [Hs | [Hs | Hs]].
    + exact (proj2 (HF' a (HF a (or_introl Hs))) HI).
    + pose proof (HSH Hs). unfold kLowMemEnd in *. lia.
    + exact (proj2 (HF' a (HF a (or_intror Hs))) HI).
  - (* a side frame of Sc *)
    destruct (frame_facts B lyc Sc _ c q M Hin) as (Cc & Cp & _ & _ & _ & P1 & P2 & _).
    pose proof (Z.mul_nonneg_nonneg c (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
    cbn [fst snd] in Hr.
    destruct HS as [Hs | [Hs | Hs]].
    + assert (NE : (c, q) <> (cid, pos)) by (intros E; rewrite E in Hin; exact (NIN Hin)).
      pose proof (frames_apart c q cid pos Cc Cp Hc Hp NE) as D.
      unfold frame_rng, in_zr, frame_addr, zdisjoint in *. cbn [fst snd] in *. lia.
    + assert (FINcq : in_app (frame_addr lyc c q) (fs_frame_bytes c)).
      { apply (in_app_sub (ly_F lyc) kFakeStackSize); [exact FA | | lia |];
          unfold frame_addr, kFakeFramesOff in *; lia. }
      refine (app_vs_shadow (frame_addr lyc c q) (fs_frame_bytes c) (frame_addr lyc cid pos) (fs_frame_bytes cid) a
        FINcq FIN ltac:(lia) Hr _). unfold in_zr in Hs. cbn [fst snd] in Hs. exact Hs.
    + subst a. unfold flag_addr, frame_addr, kFakeFlagsOff, kFakeFramesOff in *. lia.
Qed.

Lemma akb_not_side : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos a,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames Sc) ->
  akb segs B lyc Sc slo shi a -> ~ aside_rng lyc cid pos a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos a HJ Hc Hp NIN Hb.
  exact (sclass_not_side G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k cid pos a HJ Hc Hp NIN
    (sclass_of_akb lyc Sc slo shi a Hb)).
Qed.

(* The same for every byte of a range of the read set. *)
Lemma akb_range_not_side : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos
    (Rd : Z -> Prop) a,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames Sc) ->
  (forall x, Rd x -> akb segs B lyc Sc slo shi x) -> Rd a -> ~ aside_rng lyc cid pos a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos Rd a HJ Hc Hp NIN HR Ha.
  exact (akb_not_side G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos a HJ Hc Hp NIN
    (HR a Ha)).
Qed.

(* A byte of the caller's write set (apre's ajw) that is an application byte or an image byte is not a byte of a
   side frame that is free at the call (e.g. the marks block against reac_served_unmark_all's own frame). *)
Lemma ajw_not_side : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k cid pos a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames Sc) ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a -> (a < kLowMemEnd \/ kHighMemBeg <= a) ->
  ~ aside_rng lyc cid pos a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k cid pos a HG HJ Hc Hp NIN Hw Ha.
  exact (sclass_not_side G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k cid pos a HJ Hc Hp NIN
    (sclass_of_ajw G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HG HJ Hw Ha)).
Qed.

End a.

(* No global sink_head instance is in scope here, so every journal above is the Section's own SK. *)
Fail Definition sink_head_probe_shadow : YI16.sink_head := _.
