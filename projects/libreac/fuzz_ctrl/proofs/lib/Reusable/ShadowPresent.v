(* lib/Reusable/ShadowPresent.v -- image-generic: presence of visible bytes is preserved across machine steps and across
   the runtime-contract posts that state it.  Written by a Theorem Labs lane for a Theorem Labs lane (two Theorem Labs lanes
   ruling 03:20Z).  proves no function (kind: segment lemma).

   Purpose.  ProgWorld's named gap AR_states_vis0_shadow (lib/A/ProgWorld.v Section ShadowGap): every visible shadow byte
   in a vis0 zone is present in raw memory.  It is discharged by START-UP (a Theorem Labs lane's KRWLAZY shadow rows,
   A/AB01.v, the HS_tfib_ rows) and STEP = presence preservation, which this file gives.  The view alone cannot give it: ahs_pres
   (YG0n.v:442-444) excludes exactly the visible in_vis0 case, and no ARm view field covers the shadow of T, NB, SB, C, D,
   Q, the region-info page, ly_extra or F's non-frame part (a Theorem Labs lane, 03:1xZ).

   Every lemma is over an arbitrary address set P (for ProgWorld: in_shadow a /\ in_vis0 ly a), so nothing here depends
   on an image.

   Which contract posts preserve presence (measured on a working branch 7c7900ae455):
   - Machine runs: YI04.msteps (shadow_present_steps) and YK04R.fsteps (shadow_present_fsteps): memory only grows.
   - Posts with the presence-monotone clause `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a`, all with
     W' = W: aintrin_realizes OCpy / OSet (YG0d.v:336), amemcmp_realizes (:352), abcmp_realizes (:372),
     amemchr0_realizes (:401), astrnlen_realizes (:420).  Lemma: shadow_present_of_apresent_mono.
   - astack_free_law (YG0d.v:301-309): its own premise :306 (`forall a, aview .. mem a <> None -> aview .. mem' a <>
     None`) with seg_rom_none_of_AR (a shadow address lies above every segment).  Lemma: shadow_present_of_view_mono.
   NOT DERIVABLE -- the post lacks a clause (no lemma is stated for these; reported to a Theorem Labs lane for a Theorem Labs lane):
   - amalloc04_rule / afree04_rule (YC5d.v:57-97).  The post is ajournal + acall_kept.  acall_kept's presence clause
     (YCbq.v:834) covers only alloc_ceiling <= a, and alloc_ceiling >= CEIL_MIN = 0x7fff7f800000 (YM05.v:11, 19), above
     both shadow bands; its view clauses (:826-833) cover a >= alloc_ceiling, block bytes, image bytes and the shadow of
     live fake frames, not the vis0 shadow; ajournal's presence clause (YCbq.v:368) covers only the stack window.
     MISSING CLAUSE in acall_kept: `(forall a, apresent (w_H W) memc a -> apresent (w_H W2) mem2 a)`.
   - astack_malloc_realizes (YG0d.v:285-300).  Presence is stated only over the new frame (:297) and the callee window
     (:300); the frame condition (:298-299) covers only bytes not owned before and after, and every vis0 shadow byte is
     owned (aowned's shadow-of-zone disjunct over lm_zone / hm_zone, YG0n.v:236-241).
     MISSING CLAUSE in its post: `(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)`.
   Both clauses hold of the real code (no instruction removes a byte: YI04.step_mem_grows), so adding them is sound;
   with them, shadow_present_of_apresent_mono applies unchanged (for acall_kept with H = w_H W, H' = w_H W2). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six twin modules (YI04 YI16 YK11 YK1b YM05 YO09) are Required by their CORE path and every use below is spelled
   lib.Reusable.X (porter rules 04:24Z / 04:33Z), unambiguous in any consumer whose closure also loads lib/A's copies. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK1b YI04 YK0i YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG0f Reusable.YG0n Reusable.YG0q.
Local Open Scope Z_scope.

Section ShadowPresent.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable segs : list Segment.
Variable B : YG0f.asyms.

(* ---- machine runs ---- *)

Lemma fsteps_mem_grows : forall RNG ms ms',
  YK04R.fsteps segs RNG ms ms' -> lib.Reusable.YK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros RNG ms ms' Hrun. induction Hrun as [ms | ms ms1 ms2 [_ (accs & Hs & _)] _ IH].
  - apply lib.Reusable.YK1b.mem_grows_refl.
  - eapply lib.Reusable.YK1b.mem_grows_trans; [|exact IH].
    apply (lib.Reusable.YI04.step_mem_grows segs). unfold RiscvSemantics.step, drop_access_report. rewrite Hs. reflexivity.
Qed.

Lemma shadow_present_steps : forall (s s' : machine_state) (P : Z -> Prop),
  YK0i.msteps segs s s' ->
  (forall a, P a -> ms_mem s (Z_to_bv 64 a) <> None) ->
  forall a, P a -> ms_mem s' (Z_to_bv 64 a) <> None.
Proof. intros s s' P Hs H0 a Ha. exact (lib.Reusable.YI04.msteps_mem_grows segs s s' Hs _ (H0 a Ha)). Qed.

Lemma shadow_present_fsteps : forall RNG (s s' : machine_state) (P : Z -> Prop),
  YK04R.fsteps segs RNG s s' ->
  (forall a, P a -> ms_mem s (Z_to_bv 64 a) <> None) ->
  forall a, P a -> ms_mem s' (Z_to_bv 64 a) <> None.
Proof. intros RNG s s' P Hs H0 a Ha. exact (fsteps_mem_grows RNG s s' Hs _ (H0 a Ha)). Qed.

(* ---- contract posts ---- *)

(* aintrin (OCpy / OSet), amemcmp, abcmp, amemchr0, astrnlen: the post's last conjunct is the first premise. *)
Lemma shadow_present_of_apresent_mono : forall (H H' : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  (forall a, YG0n.apresent H m a -> YG0n.apresent H' m' a) ->
  (forall a, P a -> H (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) <> None) ->
  forall a, P a -> H (Z_to_bv 64 a) = false -> m' (Z_to_bv 64 a) <> None.
Proof.
  intros H H' m m' P Hmono H0 a Ha Hh.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [|exact (False_ind _ (H0 a Ha Hh Eb))].
  destruct (Hmono a (conj Hh (ex_intro _ b Eb))) as (_ & b' & Eb').
  rewrite Eb'. discriminate.
Qed.

(* astack_free_law: its premise YG0d.v:306 is the first premise; the second is seg_rom_none_of_AR for shadow bytes. *)
Lemma shadow_present_of_view_mono : forall (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  (forall a, YG0n.aview segs H m a <> None -> YG0n.aview segs H m' a <> None) ->
  (forall a, P a -> lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = None) ->
  (forall a, P a -> H (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) <> None) ->
  forall a, P a -> H (Z_to_bv 64 a) = false -> m' (Z_to_bv 64 a) <> None.
Proof.
  intros H m m' P Hmono Hrom H0 a Ha Hh.
  assert (Hv : YG0n.aview segs H m a <> None).
  { unfold YG0n.aview, YP09.mbyte, YK04.mrestrict. rewrite Hh.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [discriminate | exact (False_ind _ (H0 a Ha Hh Eb))]. }
  specialize (Hmono a Hv). unfold YG0n.aview, YP09.mbyte, YK04.mrestrict in Hmono. rewrite Hh in Hmono.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [discriminate|].
  rewrite (Hrom a Ha) in Hmono. exfalso. exact (Hmono eq_refl).
Qed.

(* No read-only byte above kImgEnd = 0x677000 (hence none at any shadow address) in an AR state. *)
Lemma seg_rom_none_of_AR : forall ly S (W : YA0n.world segs) m md,
  YG0n.AR segs B ly S W m md ->
  forall a, YG0f.kImgEnd <= a < 2 ^ 64 -> lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a) = None.
Proof.
  intros ly S W m md HAR a Ha.
  destruct HAR as (HARm & HL & _).
  assert (Himg : forall sg, In sg segs -> fst (YG0f.ly_img ly) <= Z.of_N (seg_base sg) /\
            Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (YG0f.ly_img ly) + snd (YG0f.ly_img ly))
    by (destruct HL; assumption).
  assert (Hlay : YG0f.layout_ok ly) by (destruct HARm; assumption).
  assert (Hlo : fst (YG0f.ly_img ly) = YG0f.kImgLo /\ 0 < snd (YG0f.ly_img ly) /\
                YG0f.kImgLo + snd (YG0f.ly_img ly) <= YG0f.kImgEnd /\ YG0f.page_aligned (snd (YG0f.ly_img ly)))
    by (destruct Hlay; assumption).
  apply (YG0q.seg_rom_none_above segs a); [|exact Ha].
  intros sg Hin. destruct (Himg sg Hin) as [G1 G2]. destruct Hlo as (L1 & _ & L3 & _).
  unfold YG0f.kImgLo in L1, L3. lia.
Qed.

End ShadowPresent.
