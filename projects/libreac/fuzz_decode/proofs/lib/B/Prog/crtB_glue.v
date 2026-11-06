(* crtB_glue: the small facts that carry cgif's world-level memory facts (apresent, aview, acall_kept) to the
   decode-level facts the footprint runs of lib/B/Prog/crtB_segs.v take (stk, rw_cells, ExecF.rng), and back, for
   the pieces of the cgif-form walk of check_round_trip on image B.  Nothing here is image-B specific except
   crtB_segs_low (the image's segments are all below kLowMemEnd, by vm_compute) and the segment list. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YK06.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YK1b YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
Import ListNotations.
Open Scope Z_scope.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.

(* Every loaded segment of image B lies below kLowMemEnd: the Hypothesis `segs_low` of lib/Reusable/YCbq.v:208. *)
Lemma crtB_segs_low : forall a, in_img decodesegsB0 a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr).
  assert (Hall : forallb (fun s => (0 <=? Z.of_N (seg_base s)) &&
                   (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))%bool decodesegsB0 = true)
    by (clear; vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hall sg Hin) as Hs. cbv beta in Hs.
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* A visible present byte is the byte decode's mrd reads. *)
Lemma crtB_mrd_of_apresent : forall H mem a, apresent H mem a -> exists b, mrd rsegs mem (wa a) = Some b.
Proof.
  intros H mem a [Hh [b Hb]]. exists b. unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma crtB_wview_some : forall mem (x : word) b, mem x = Some b -> wview rsegs mem x <> None.
Proof. intros mem x b Hm. unfold wview. rewrite Hm. discriminate. Qed.

Lemma crtB_wview_of_apresent : forall H mem a, apresent H mem a -> wview rsegs mem (wa a) <> None.
Proof. intros H mem a [Hh [b Hb]]. exact (crtB_wview_some mem (wa a) b Hb). Qed.

(* decode's `stk` (lib/Lib/Frame.v:144) over a window of visible present bytes. *)
Lemma crtB_stk_of : forall H mem lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent H mem a) -> stk rsegs mem lo hi.
Proof.
  intros H mem lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. pose proof (Hp a Ha) as Hpa.
  split; [exact (crtB_wview_of_apresent H mem a Hpa) | exact (crtB_mrd_of_apresent H mem a Hpa)].
Qed.

(* decode's `wr_at` over the same window. *)
Lemma crtB_wr_at_of : forall H mem lo n,
  0 <= lo -> lo + n <= 2 ^ 64 -> (forall a, lo <= a < lo + n -> apresent H mem a) -> wr_at rsegs mem lo n.
Proof.
  intros H mem lo n Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros i Hi. exact (crtB_wview_of_apresent H mem (lo + i) (Hp (lo + i) ltac:(lia))).
Qed.

(* The walk's footprint (all visible bytes) holds a window of visible bytes. *)
Lemma crtB_rng_of_vis : forall (W : world decodesegsB0) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> w_H W (wa a) = false) ->
  ExecF.rng (LCK.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W) lo len.
Proof.
  intros W lo len Hlo Hhi Hv. split; [exact Hlo|]. split; [exact Hhi|].
  intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff.
  intros k Hk.
  assert (Hbr : 0 <= b < 2 ^ 64) by lia.
  rewrite (unsigned_lit b Hbr).
  change (Z_to_bv 64 (b + Z.of_nat k)) with (wa (b + Z.of_nat k)).
  apply Hv. lia.
Qed.

Lemma crtB_rng_of_apresent : forall (W : world decodesegsB0) mem lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> apresent (w_H W) mem a) ->
  ExecF.rng (LCK.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W) lo len.
Proof.
  intros W mem lo len Hlo Hhi Hp. apply crtB_rng_of_vis; [exact Hlo | exact Hhi|].
  intros a Ha. exact (proj1 (Hp a Ha)).
Qed.

(* aview at a visible byte is decode's mrd of that byte. *)
Lemma crtB_aview_mrd : forall (H : word -> bool) mem a,
  H (wa a) = false ->
  aview decodesegsB0 H mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)).
Proof.
  intros H mem a Hh. unfold wa in Hh.
  unfold aview, mbyte, mrestrict, mrd, wa. rewrite Hh. reflexivity.
Qed.

Lemma crtB_opt_byte_eq : forall (x y : option byte),
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [x|] [y|] E; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* Two states that agree on aview at a visible byte agree on decode's mrd there. *)
Lemma crtB_mrd_eq_of_aview : forall (H H' : word -> bool) mem mem' a,
  H (wa a) = false -> H' (wa a) = false ->
  aview decodesegsB0 H' mem' a = aview decodesegsB0 H mem a ->
  mrd rsegs mem' (wa a) = mrd rsegs mem (wa a).
Proof.
  intros H H' mem mem' a Hh Hh' E. apply crtB_opt_byte_eq.
  rewrite <- (crtB_aview_mrd H' mem' a Hh'), <- (crtB_aview_mrd H mem a Hh). exact E.
Qed.

(* decode's cell list is kept by a state that keeps aview and presence over its bytes. *)
Lemma crtB_bytes_at_kept : forall (H H' : word -> bool) mem mem' A bs,
  bytes_at rsegs mem A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> H (wa a) = false /\ H' (wa a) = false /\
     aview decodesegsB0 H' mem' a = aview decodesegsB0 H mem a) ->
  bytes_at rsegs mem' A bs.
Proof.
  intros H H' mem mem' A bs (HA & Hlen & Hb) Hk.
  split; [exact HA|]. split; [exact Hlen|].
  intros i Hi.
  destruct (Hk (A + Z.of_nat i) ltac:(lia)) as (Hh & Hh' & Ha).
  rewrite (crtB_mrd_eq_of_aview H H' mem mem' (A + Z.of_nat i) Hh Hh' Ha). exact (Hb i Hi).
Qed.

Lemma crtB_rw_cells_kept : forall (W W' : world decodesegsB0) mem mem' A cs,
  rw_cells rsegs mem A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> apresent (w_H W) mem a /\ apresent (w_H W') mem' a /\
     aview decodesegsB0 (w_H W') mem' a = aview decodesegsB0 (w_H W) mem a) ->
  rw_cells rsegs mem' A cs.
Proof.
  intros W W' mem mem' A cs [[Hwf Hba] Hw] Hk.
  assert (Hlen : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact Hwf).
  split; [split; [exact Hwf|]|].
  - eapply (crtB_bytes_at_kept (w_H W) (w_H W') mem mem' A (cells_bytes cs) Hba).
    intros a Ha. rewrite Hlen in Ha. destruct (Hk a Ha) as (H1 & H2 & H3).
    split; [exact (proj1 H1)|]. split; [exact (proj1 H2) | exact H3].
  - pose proof Hw as (HA & Hhi & _).
    apply (crtB_wr_at_of (w_H W') mem' A (Z.of_nat (cells_size cs))); [exact HA | exact Hhi|].
    intros a Ha. exact (proj1 (proj2 (Hk a Ha))).
Qed.

(* ---- the shape of a run's final state, and that a run only grows memory ---- *)
(* Port of a working branch 9391072eea4 lib/B/Prog/LeafCgGlue.v eqv_MS_mkst
   (that file is not on this branch): a state register-equivalent to decode's MS form is cgif's mkst state of its
   own register map, at the float state the run left. *)
Lemma crtB_eqv_mkst : forall R F pc fc m ro ms,
  Regs6ss.ms_eqv (MS R F pc fc None m ro) ms ->
  ms = @YK11.mkst (YK11.mkFP F fc) (ms_regs ms) pc m ro.
Proof.
  intros R F pc fc m ro [r f p s v c mm rr] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. reflexivity.
Qed.

(* Port of LeafCgGlue.v mstepsF_grows / evtF_eqv's third conjunct. *)
Lemma crtB_mstepsF_grows : forall RNG ms ms',
  ExecF.mstepsF rsegs RNG ms ms' -> YK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros RNG ms ms' HT. induction HT as [m|m m1 m2 HS HT IH].
  - apply YK1b.mem_grows_refl.
  - eapply YK1b.mem_grows_trans; [|exact IH].
    eapply YI04.step_mem_grows. exact (ExecF.mstepF_step rsegs RNG m m1 HS).
Qed.

Lemma crtB_evtF_grows : forall RNG (P : machine_state -> Prop) ms,
  ExecF.evtF rsegs RNG P ms ->
  ExecF.evtF rsegs RNG (fun ms' => P ms' /\ YK1b.mem_grows (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros RNG P ms (ms' & HT & HP). exists ms'. split; [exact HT|].
  split; [exact HP | exact (crtB_mstepsF_grows RNG ms ms' HT)].
Qed.

Lemma crtB_mem_grows_restrict : forall (H : word -> bool) m m',
  YK1b.mem_grows m m' -> YK1b.mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' HG x Hx. unfold mrestrict in Hx |- *.
  destruct (H x); [exact Hx | exact (HG x Hx)].
Qed.
