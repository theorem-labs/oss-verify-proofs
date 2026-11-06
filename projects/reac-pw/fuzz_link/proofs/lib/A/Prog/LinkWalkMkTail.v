(* reac-pw/fuzz_link, image A: a TAIL JUMP into an own contract of the fx shape (link_amem.v aleaf_fx /
   aleaf_alloc_fx), for the walks of the marking slice: mark_quietly +0x70 `j reac_served_mark` (0x88444).

   At the jump the caller has popped its frame and restored ra and the callee-saved registers, so the callee runs
   on the caller's own sp and returns to the caller's own ra. The callee's apostF is relative to the state at the
   jump (allocator state Sj, memory memj, journal index kj); `apostF_tail` turns it into the caller's apostF
   relative to the caller's entry, given what the caller's walk knows of the jump state relative to its entry:
   - the jump state's journal index plus the callee's EV is the caller's index plus the caller's EV;
   - the return address and the callee-saved registers are the entry's, and the callee's window lies inside the
     caller's ([spZ regsj - K2, spZ regsj) inside [spZ regs - K1, spZ regs), above the allocator's ceiling);
   - the side stack, the descriptors and the file system are the entry's; every block of the entry is a block of
     the jump state (same layout lyc);
   - the caller's own kept clause and heap-block shadow clause from the entry to the jump, with its write set E1;
   - the callee's write set E2 inside E1;
   - the caller's Q1 from the callee's Q2 at the return, given the callee's kept clause.
   Both apostF are at the walk's FP state: the callee's fx' is the caller's.
   `apostF_tail_ly` (with `akept_tail_ly`, `ashadow_kept_tail_ly`) is the same for a jump state of another layout
   lyj (an allocation between entry and jump, as on mark_quietly's opening arm): it asks also ly_F lyj = ly_F lyc
   (the side-stack base; every journal's layout_le gives it), and lets the callee's write set exceed the caller's by
   bytes no clause of the caller's kept clause speaks of (`akept_out`, e.g. a block allocated since the entry).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.

(* the caller's kept clause to the jump, then the callee's from the jump: the caller's kept clause to the return *)
Lemma akept_tail : forall lyc Sc Sj W memc Wj memj W2 mem2 lo1 hi1 lo2 hi2 (E1 E2 : Z -> Prop),
  lo1 <= lo2 -> hi2 <= hi1 -> alloc_ceiling <= lo1 -> hi1 < 2 ^ 64 ->
  frames Sj = frames Sc ->
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyc Sj)) ->
  (forall a, E2 a -> E1 a) ->
  akept segs B lyc Sc W memc Wj memj lo1 hi1 E1 ->
  akept segs B lyc Sj Wj memj W2 mem2 lo2 hi2 E2 ->
  akept segs B lyc Sc W memc W2 mem2 lo1 hi1 E1.
Proof.
  intros lyc Sc Sj W memc Wj memj W2 mem2 lo1 hi1 lo2 hi2 E1 E2 Hlo Hhi Hceil Htop Hfr HB HE
    (A1 & B1 & C1 & D1 & P1 & R1) (A2 & B2 & C2 & D2 & P2 & R2).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn HEa.
    rewrite (A2 a Ha ltac:(intros Hc; apply Hn; lia) (fun h => HEa (HE a h))). exact (A1 a Ha Hn HEa).
  - intros b n i Hin Hi HEa.
    rewrite (B2 b n i (HB b n Hin) Hi (fun h => HEa (HE _ h))). exact (B1 b n i Hin Hi HEa).
  - intros a Hi Hno Herr HEa.
    rewrite (C2 a Hi Hno Herr (fun h => HEa (HE a h))). exact (C1 a Hi Hno Herr HEa).
  - intros cid pos a Hin Hr HEa.
    assert (Hin' : In (cid, pos) (frames Sj)) by (rewrite Hfr; exact Hin).
    rewrite (D2 cid pos a Hin' Hr (fun h => HEa (HE a h))). exact (D1 cid pos a Hin Hr HEa).
  - intros a Ha Hn Hp.
    exact (P2 a Ha ltac:(intros Hc; apply Hn; lia) (P1 a Ha Hn Hp)).
  - intros a Ha.
    destruct (Z_lt_le_dec a lo2) as [H1 | H1]; [|destruct (Z_lt_le_dec a hi2) as [H2 | H2]].
    + exact (P2 a ltac:(lia) ltac:(lia) (R1 a Ha)).
    + exact (R2 a ltac:(lia)).
    + exact (P2 a ltac:(lia) ltac:(lia) (R1 a Ha)).
Qed.

(* the caller's heap-block shadow clause to the jump, then the callee's: the caller's to the return *)
Lemma ashadow_kept_tail : forall lyc Sc Sj ly2 S2 W memc Wj memj W2 mem2,
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyc Sj)) ->
  ashadow_kept segs B lyc Sc lyc Sj W memc Wj memj ->
  ashadow_kept segs B lyc Sj ly2 S2 Wj memj W2 mem2 ->
  ashadow_kept segs B lyc Sc ly2 S2 W memc W2 mem2.
Proof.
  intros lyc Sc Sj ly2 S2 W memc Wj memj W2 mem2 HB HS1 HS2 b n a H1 H2 Ha.
  rewrite (HS2 b n a (HB b n H1) H2 Ha). exact (HS1 b n a H1 (HB b n H1) Ha).
Qed.

Lemma apostF_tail : forall K1 EV1 (E1 : Z -> Prop) K2 EV2 (E2 : Z -> Prop)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    Sj Wj memj mdj kj (regsj : bvmap 5 word)
    (Q1 Q2 : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (cj : config),
  kj + EV2 = k + EV1 ->
  getr regsj 1 = getr regs 1 -> aregs_preserved regs regsj ->
  spZ regs - K1 <= spZ regsj - K2 -> spZ regsj <= spZ regs -> alloc_ceiling <= spZ regs - K1 ->
  frames Sj = frames Sc -> m_fds mdj = m_fds mdc -> m_fs mdj = m_fs mdc ->
  akept segs B lyc Sc W memc Wj memj (spZ regs - K1) (spZ regs) E1 ->
  ashadow_kept segs B lyc Sc lyc Sj W memc Wj memj ->
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyc Sj)) ->
  (forall a, E2 a -> E1 a) ->
  (forall ly2 S2 W2 regs2 mem2 md2, wle Wj W2 ->
     akept segs B lyc Sj Wj memj W2 mem2 (spZ regsj - K2) (spZ regsj) E2 ->
     Q2 ly2 S2 W2 regs2 mem2 md2 -> Q1 ly2 S2 W2 regs2 mem2 md2) ->
  SRr segs Wj cj (apostF SK segs B K2 EV2 E2 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sj Wj memj mdj kj
    regsj Q2) ->
  SRr segs Wj cj (apostF SK segs B K1 EV1 E1 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs Q1).
Proof.
  intros K1 EV1 E1 K2 EV2 E2 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    Sj Wj memj mdj kj regsj Q1 Q2 cj
    Hk Hra Hrp Hw1 Hw2 Hceil Hfr Hfd Hfs HK1 HS1 HB HE HQ HSR.
  pose proof (bv_unsigned_in_range _ (getr regs 2)) as Hsp. unfold bv_modulus in Hsp. cbn [Z.of_N] in Hsp.
  assert (Htop : spZ regs < 2 ^ 64) by (unfold spZ; lia).
  eapply SRr_mono; [exact HSR|].
  intros W2 c2 Hle (fx' & Hfx & ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & HP & Hfr2 & Hfd2 & Hfs2 & HK2 & HS2 & HQ2).
  exists fx'. split; [exact Hfx|].
  exists ly2, S2, regs2, mem2, md2.
  split; [rewrite Hc, Hra; reflexivity|].
  split; [rewrite <- Hk; exact HJ|].
  split; [exact (aregs_preserved_trans _ _ _ Hrp HP)|].
  split; [rewrite Hfr2; exact Hfr|].
  split; [rewrite Hfd2; exact Hfd|].
  split; [rewrite Hfs2; exact Hfs|].
  split; [exact (akept_tail lyc Sc Sj W memc Wj memj W2 mem2 _ _ _ _ E1 E2 Hw1 Hw2 Hceil Htop Hfr HB HE HK1 HK2)|].
  split; [exact (ashadow_kept_tail lyc Sc Sj ly2 S2 W memc Wj memj W2 mem2 HB HS1 HS2)|].
  exact (HQ ly2 S2 W2 regs2 mem2 md2 Hle HK2 HQ2).
Qed.

(* THE SAME AT A JUMP STATE OF ANOTHER LAYOUT lyj (an allocation between the entry and the jump, mark_quietly's
   opening arm): the side-stack base is the entry's (ly_F lyj = ly_F lyc; every journal's layout_le gives it), the
   frames are the entry's, and every block of the entry is a block of the jump state. The callee may write bytes
   outside the caller's write set when no clause of the caller's kept clause speaks of them (`akept_out`: below the
   allocator's ceiling, off the image, in no block and no side frame of the entry; a block allocated since). *)
Definition akept_out (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ~ in_img segs a /\
  (forall b m, In (b, m) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size m)) /\
  (forall cid pos, In (cid, pos) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (cid, pos)) /\ ~ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).

Lemma akept_tail_ly : forall lyc Sc lyj Sj W memc Wj memj W2 mem2 lo1 hi1 lo2 hi2 (E1 E2 : Z -> Prop),
  lo1 <= lo2 -> hi2 <= hi1 -> alloc_ceiling <= lo1 -> hi1 < 2 ^ 64 ->
  ly_F lyj = ly_F lyc -> frames Sj = frames Sc ->
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyj Sj)) ->
  (forall a, E2 a -> E1 a \/ akept_out lyc Sc a) ->
  akept segs B lyc Sc W memc Wj memj lo1 hi1 E1 ->
  akept segs B lyj Sj Wj memj W2 mem2 lo2 hi2 E2 ->
  akept segs B lyc Sc W memc W2 mem2 lo1 hi1 E1.
Proof.
  intros lyc Sc lyj Sj W memc Wj memj W2 mem2 lo1 hi1 lo2 hi2 E1 E2 Hlo Hhi Hceil Htop HF Hfr HB HE
    (A1 & B1 & C1 & D1 & P1 & R1) (A2 & B2 & C2 & D2 & P2 & R2).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn HEa.
    assert (N2 : ~ E2 a) by (intros h; destruct (HE a h) as [h1 | (h1 & _)]; [exact (HEa h1) | lia]).
    rewrite (A2 a Ha ltac:(intros Hc; apply Hn; lia) N2). exact (A1 a Ha Hn HEa).
  - intros b n i Hin Hi HEa.
    assert (N2 : ~ E2 (b + i))
      by (intros h; destruct (HE _ h) as [h1 | (_ & _ & h1 & _)]; [exact (HEa h1) | exact (h1 b n Hin ltac:(lia))]).
    rewrite (B2 b n i (HB b n Hin) Hi N2). exact (B1 b n i Hin Hi HEa).
  - intros a Hi Hno Herr HEa.
    assert (N2 : ~ E2 a) by (intros h; destruct (HE a h) as [h1 | (_ & h1 & _)]; [exact (HEa h1) | exact (h1 Hi)]).
    rewrite (C2 a Hi Hno Herr N2). exact (C1 a Hi Hno Herr HEa).
  - intros cid pos a Hin Hr HEa.
    assert (Hin' : In (cid, pos) (frames Sj)) by (rewrite Hfr; exact Hin).
    assert (Hr' : in_zr a (frame_rng lyj (cid, pos)) \/
                  in_zr a (shadow_addr (frame_addr lyj cid pos), fs_frame_bytes cid / 8))
      by (unfold frame_rng, frame_addr in *; rewrite HF; exact Hr).
    assert (N2 : ~ E2 a).
    { intros h. destruct (HE a h) as [h1 | (_ & _ & _ & h1)]; [exact (HEa h1)|].
      destruct (h1 cid pos Hin) as (h2 & h3). destruct Hr as [Hr | Hr]; [exact (h2 Hr) | exact (h3 Hr)]. }
    rewrite (D2 cid pos a Hin' Hr' N2). exact (D1 cid pos a Hin Hr HEa).
  - intros a Ha Hn Hp.
    exact (P2 a Ha ltac:(intros Hc; apply Hn; lia) (P1 a Ha Hn Hp)).
  - intros a Ha.
    destruct (Z_lt_le_dec a lo2) as [H1 | H1]; [|destruct (Z_lt_le_dec a hi2) as [H2 | H2]].
    + exact (P2 a ltac:(lia) ltac:(lia) (R1 a Ha)).
    + exact (R2 a ltac:(lia)).
    + exact (P2 a ltac:(lia) ltac:(lia) (R1 a Ha)).
Qed.

Lemma ashadow_kept_tail_ly : forall lyc Sc lyj Sj ly2 S2 W memc Wj memj W2 mem2,
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyj Sj)) ->
  ashadow_kept segs B lyc Sc lyj Sj W memc Wj memj ->
  ashadow_kept segs B lyj Sj ly2 S2 Wj memj W2 mem2 ->
  ashadow_kept segs B lyc Sc ly2 S2 W memc W2 mem2.
Proof.
  intros lyc Sc lyj Sj ly2 S2 W memc Wj memj W2 mem2 HB HS1 HS2 b n a H1 H2 Ha.
  rewrite (HS2 b n a (HB b n H1) H2 Ha). exact (HS1 b n a H1 (HB b n H1) Ha).
Qed.

Lemma apostF_tail_ly : forall K1 EV1 (E1 : Z -> Prop) K2 EV2 (E2 : Z -> Prop)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    lyj Sj Wj memj mdj kj (regsj : bvmap 5 word)
    (Q1 Q2 : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (cj : config),
  kj + EV2 = k + EV1 ->
  getr regsj 1 = getr regs 1 -> aregs_preserved regs regsj ->
  spZ regs - K1 <= spZ regsj - K2 -> spZ regsj <= spZ regs -> alloc_ceiling <= spZ regs - K1 ->
  ly_F lyj = ly_F lyc -> frames Sj = frames Sc -> m_fds mdj = m_fds mdc -> m_fs mdj = m_fs mdc ->
  akept segs B lyc Sc W memc Wj memj (spZ regs - K1) (spZ regs) E1 ->
  ashadow_kept segs B lyc Sc lyj Sj W memc Wj memj ->
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyj Sj)) ->
  (forall a, E2 a -> E1 a \/ akept_out lyc Sc a) ->
  (forall ly2 S2 W2 regs2 mem2 md2, wle Wj W2 ->
     akept segs B lyj Sj Wj memj W2 mem2 (spZ regsj - K2) (spZ regsj) E2 ->
     Q2 ly2 S2 W2 regs2 mem2 md2 -> Q1 ly2 S2 W2 regs2 mem2 md2) ->
  SRr segs Wj cj (apostF SK segs B K2 EV2 E2 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyj Sj Wj memj mdj kj
    regsj Q2) ->
  SRr segs Wj cj (apostF SK segs B K1 EV1 E1 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs Q1).
Proof.
  intros K1 EV1 E1 K2 EV2 E2 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    lyj Sj Wj memj mdj kj regsj Q1 Q2 cj
    Hk Hra Hrp Hw1 Hw2 Hceil HF Hfr Hfd Hfs HK1 HS1 HB HE HQ HSR.
  pose proof (bv_unsigned_in_range _ (getr regs 2)) as Hsp. unfold bv_modulus in Hsp. cbn [Z.of_N] in Hsp.
  assert (Htop : spZ regs < 2 ^ 64) by (unfold spZ; lia).
  eapply SRr_mono; [exact HSR|].
  intros W2 c2 Hle (fx' & Hfx & ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & HP & Hfr2 & Hfd2 & Hfs2 & HK2 & HS2 & HQ2).
  exists fx'. split; [exact Hfx|].
  exists ly2, S2, regs2, mem2, md2.
  split; [rewrite Hc, Hra; reflexivity|].
  split; [rewrite <- Hk; exact HJ|].
  split; [exact (aregs_preserved_trans _ _ _ Hrp HP)|].
  split; [rewrite Hfr2; exact Hfr|].
  split; [rewrite Hfd2; exact Hfd|].
  split; [rewrite Hfs2; exact Hfs|].
  split; [exact (akept_tail_ly lyc Sc lyj Sj W memc Wj memj W2 mem2 _ _ _ _ E1 E2 Hw1 Hw2 Hceil Htop HF Hfr HB HE
                   HK1 HK2)|].
  split; [exact (ashadow_kept_tail_ly lyc Sc lyj Sj ly2 S2 W memc Wj memj W2 mem2 HB HS1 HS2)|].
  exact (HQ ly2 S2 W2 regs2 mem2 md2 Hle HK2 HQ2).
Qed.

End t.
