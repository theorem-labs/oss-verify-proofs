(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the caller's journal across a lifted stretch (a Theorem Labs lane glue).

   A lifted stretch (A/Prog/GE_lift.v, GE_entry.v) hands its continuation the lib.Lib facts of the run:
   `munch WR memc m'` (the run writes only inside the ranges WR), `wmono rsegs memc m'` (no writable byte is
   removed) and the hidden bytes unchanged (Reusable/YA0nR.v `SRr_fevt_hid`). The core's `ajournal_exec`
   (Reusable/YCbq.v:636) carries the caller's journal across a write, but over the world's restricted memory
   (`mrestrict (w_H W) _`, `mem_grows`). This file is the bridge between the two.

   - `ge_view_of_munch`: outside WR, the reader of the world is the same before and after the run.
   - `ge_awr_not_img`: a byte the caller lets the call write is not image memory.
   - `ge_jrnl`: the journal survives a run that writes inside WR, when every byte of WR is one the caller
     lets the call write (`awr_byte`).
   - `ge_jrnl_win`: the same, for WR = the stretch's own stack window and the output buffer [q, q + len).
   - `ge_ro_keep`: the read-only data (`arodata_okS`, Reusable/YE01.v:189) survives a run that writes no
     image byte.

   Why `mem_grows` needs the journal. `wmono` speaks of `wview`, which reads a writable segment's initial byte
   where the memory holds none; `mem_grows` speaks of the memory itself. The two differ only at image bytes. A
   byte the run writes is an `awr_byte` of the caller (stack window, client block, own frame or its shadow), and
   none of those is image memory (`ge_awr_not_img`); a byte the run does not write is unchanged (`munch`).

   The segment-low side condition of `ajournal_exec` is CtrlImg.v `ctrl_segs_low` (the walk's segment list is
   tfibsegs), so it is no premise here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.

Lemma ge_outside_dec : forall (WR : list ivl) (x : Z), outside WR x \/ ~ outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H | H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z.le_gt_cases lo x) as [H1 | H1]; [destruct (Z.lt_ge_cases x hi) as [H2 | H2]|].
  - right. intros [H3 _]. apply H3. split; assumption.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

(* (1) The view bridge. Outside the run's write ranges the restricted memory is unchanged, so the world's
   reader is unchanged. (A hidden byte reads None on both sides, so the hidden-byte fact is not needed.) *)
Lemma ge_view_of_munch : forall (H : word -> bool) (m m' : word -> option byte) (WR : list ivl) (a : Z),
  0 <= a < 2 ^ 64 -> munch WR m m' -> outside WR a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' WR a Ha Hmu Ho. apply (aview_eq_of SEGS). unfold mrestrict.
  destruct (H (Z_to_bv 64 a)); [reflexivity|]. apply Hmu.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Ho.
Qed.

(* A byte the caller lets the call write is not image memory: the stack window lies above alloc_ceiling, the
   client blocks and the own frames are not image (AR's client-image law), and a frame's shadow lies at or
   above kLowMemEnd, while every image byte lies below it (ctrl_segs_low). *)
Lemma ge_awr_not_img : forall (B : asyms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
  AR_laws SEGS B ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> ~ in_img SEGS a.
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a LAWS HJ Hw Hi.
  pose proof (ctrl_segs_low a Hi) as Hlow.
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)
    as (_ & [[Hc _] | [(_ & b & n & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl _] _]])]]).
  - lia.
  - exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
  - assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin Hr Hi).
  - lia.
Qed.

(* (2) + (3) The caller's journal survives a lifted stretch. *)
Lemma ge_jrnl : forall (B : asyms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (mdc' : Model) (WR : list ivl) (m' : word -> option byte),
  AR_laws SEGS B ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  munch WR memc m' -> wmono rsegs memc m' ->
  (forall x : word, w_H W x = true -> m' x = memc x) ->
  same_but_materialized mdc mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside WR a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' WR m' LAWS HJ Hmu Hwm Hhid Hsame HW.
  eapply (ajournal_exec SEGS B LAWS ctrl_segs_low) with (Wr := fun a => 0 <= a < 2 ^ 64 /\ ~ outside WR a);
    [exact HJ | | | exact Hhid | exact Hsame | ].
  - intros x Hx. cbv beta in Hx. unfold mrestrict. destruct (w_H W x); [reflexivity|].
    apply Hmu. destruct (ge_outside_dec WR (bv_unsigned x)) as [Ho | Ho]; [exact Ho|].
    exfalso. apply Hx. split; [exact (u64_range x) | exact Ho].
  - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|].
    destruct (ge_outside_dec WR (bv_unsigned x)) as [Ho | Ho]; [rewrite (Hmu x Ho); exact Hx|].
    pose proof (ge_awr_not_img B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (bv_unsigned x) LAWS HJ
      (HW _ (u64_range x) Ho)) as Hni.
    assert (Hwv : wview rsegs memc x <> None)
      by (unfold wview; destruct (memc x); [discriminate | exfalso; exact (Hx eq_refl)]).
    pose proof (Hwm x Hwv) as Hwv'. unfold wview in Hwv'. destruct (m' x); [discriminate|].
    rewrite <- ge_segs in Hwv'. rewrite (find_segment_none SEGS (bv_unsigned x) Hni) in Hwv'. exact Hwv'.
  - intros a [Ha Ho]. exact (HW a Ha Ho).
Qed.

(* The form the glue uses: the stretch writes its own stack window [sp - STK', sp), which lies inside the
   caller's window [sp0 - STK, sp0), and the output buffer [q, q + len), which the caller lets the call write
   (twr_ok, CtrlCallerJ.v). Only twr_ok's awr_byte part is used, so its world, memory and stack pointer are
   free. *)
Lemma ge_jrnl_win : forall (B : asyms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (mdc' : Model) (m' : word -> option byte) (sp STK' q len : Z)
    (Wt : world SEGS) (memt : word -> option byte) (spt : Z),
  AR_laws SEGS B ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  munch [(sp - STK', sp); (q, q + len)] memc m' -> wmono rsegs memc m' ->
  (forall x : word, w_H W x = true -> m' x = memc x) ->
  same_but_materialized mdc mdc' ->
  sp0 - STK <= sp - STK' -> sp <= sp0 ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own Wt memt spt q len ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' m' sp STK' q len Wt memt spt
    LAWS HJ Hmu Hwm Hhid Hsame Hlo Hhi Htw.
  eapply ge_jrnl; [exact LAWS | exact HJ | exact Hmu | exact Hwm | exact Hhid | exact Hsame |].
  intros a _ Ho. cbn [outside] in Ho.
  destruct (Z.le_gt_cases (sp - STK') a) as [H1 | H1]; [destruct (Z.lt_ge_cases a sp) as [H2 | H2]|].
  - unfold awr_byte. left. lia.
  - destruct (Z.le_gt_cases q a) as [H3 | H3]; [destruct (Z.lt_ge_cases a (q + len)) as [H4 | H4]|].
    + exact (proj1 (Htw a (conj H3 H4))).
    + exfalso. apply Ho. split; [lia|]. split; [lia | exact I].
    + exfalso. apply Ho. split; [lia|]. split; [lia | exact I].
  - destruct (Z.le_gt_cases q a) as [H3 | H3]; [destruct (Z.lt_ge_cases a (q + len)) as [H4 | H4]|].
    + exact (proj1 (Htw a (conj H3 H4))).
    + exfalso. apply Ho. split; [lia|]. split; [lia | exact I].
    + exfalso. apply Ho. split; [lia|]. split; [lia | exact I].
Qed.

(* The read-only data survives a run that writes no image byte. The range [rlo, rhi) lies in the image
   (C_ctrl_emit_as.v's binder RELRO_IMG has exactly this form); without it a byte of [rlo, rhi) outside
   [0, 2^64) would be read at its 64-bit wrap, which the write ranges do not speak of. *)
Lemma ge_ro_keep : forall (B : asyms) (H : word -> bool) (rlo rhi : Z) (m m' : word -> option byte) (WR : list ivl),
  (forall a, rlo <= a < rhi -> in_img SEGS a) ->
  arodata_okS SEGS B rlo rhi (aview SEGS H m) ->
  munch WR m m' ->
  (forall a, in_img SEGS a -> outside WR a) ->
  arodata_okS SEGS B rlo rhi (aview SEGS H m').
Proof.
  intros B H rlo rhi m m' WR Hrel Hro Hmu Hout a Hseg Hno He.
  assert (Hi : in_img SEGS a).
  { destruct Hseg as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | lia] | exact (Hrel a Hr)]. }
  pose proof (ctrl_segs_low a Hi) as Hlow. pose proof asan_consts as (_ & _ & _ & _ & C5).
  rewrite (ge_view_of_munch H m m' WR a ltac:(lia) Hmu (Hout a Hi)).
  exact (Hro a Hseg Hno He).
Qed.

End b.
