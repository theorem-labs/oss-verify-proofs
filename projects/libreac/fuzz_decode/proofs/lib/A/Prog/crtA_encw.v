(* crtA_encw: the ENCODE / BCMP piece of the cgif-form walk of check_round_trip, image A of libreac/fuzz_decode
   (fuzz_decode.asan): crtA_enc_piece : crtA_at_bcmp -> crtA_at_loopout (lib/A/Prog/crtA_cuts.v), the piece ENCP of
   lib/A/Prog/crtA_close.v.

   rule 24: no function proved.  This is a walk step of check_round_trip's image-A walk composed from proved callee
   contracts: reac_braid_encode's leaf contract (lib/A/Prog/reac_braid_encode_cg.v dec_reac_braid_encode_cg, a
   Section hypothesis, as in check_round_trip_cg.v:237) and bcmp's runtime contract (lib/Reusable/YG0d.v:353
   abcmp_realizes at the listing's trampoline, a Section hypothesis, as in check_round_trip_cg.v:236).

   The run, from the cut at CRT_LOOP_OUT (+0x1f0) to the cut at CRT_RET_BCMP (+0x218):
     +0x1f0 .. +0x204  the arguments of reac_braid_encode (lib/A/Prog/crtA_segs.v crt_seg5_F), a footprint run
                       carried into SRr by lib/A/Prog/crtA_walk.v crtA_run;
     reac_braid_encode its leaf contract, every premise discharged from the cut state: the cgif call frame
                       (YCbq.v:1913 ecall_pre_at on the inner journal), the stack / block presence (stk, wr_at, rng)
                       and the shadow of the three blocks (YCbq.v:2687 range_addressable_of_block, :1945
                       shadow_hull_vis_of_block) read in decode's form, the runtime cells (crtA_cells.v
                       dec_cells_asan), the planar table and samples the convert loop left (crtA_cuts.v crtA_conv),
                       the read-only FCLAMP_HI bytes (crtA_rom_on of the cut), the blocks' separation (YCbq.v:420
                       sep_blocks, and NoDup from AR_blocks_law);
     +0x208 .. +0x214  the arguments of bcmp (crt_seg6_F), again through crtA_run;
     bcmp              YCbq.v:2062 aj_bcmp_at, which keeps the inner journal; its zero answer is the braid relation:
                       the encoded rows at R are, byte for byte, the caller's audio (lib/A/Prog/crtA_enc.v crt_out
                       and crt_audio_ok over the restricted overlay, from the statement's dec_crt_braid).
   The journal is re-established across the runs by YCbq.v:636 ajournal_exec and across the leaf by YCbq.v:517
   ajournal_after_write; the frame the prologue wrote and the read-only view (crtA_rom_on) are carried to the
   bcmp cut.

   Old-form record of the same step: a working branch dc455613c81 lib/A/Prog/check_round_trip_F.v
   crt_mid_F (segments 6-7 around the encode / bcmp calls, with crt_glue.v and crt_enc.v); this file ports its
   structure into cgif's backward-chain form (cgif_file_fuzzer ACey.v:270-330 / ACet.v:36-43). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Regs6ss ExecF CrtBridge CrtEnc FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr DecodeList.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface check_round_trip_cg crtA_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_segs crtA_walk crtA_cells crtA_enc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_braid_c crt_braid_need crtA_fevt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit reac_braid_encode_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.
Module LBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_braid_encode_cg.

Section CrtEncW.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation segs := decodesegs0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis ABCMP : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc segs B (decode_sigma DS___interceptor_trampoline_bcmp).
Hypothesis ALEAF : forall fx' : YKK.FPState, dec_leaf_wr_at B (@LBraid.dec_reac_braid_encode_cg) fx'.
(* The read-only bytes the braid leaf reads (its REAC_BRAID_ENCODE_RO_RD) are among the walk's RO_RD, on which the
   cuts carry crtA_rom_on.  The close instantiates RO_RD with that list, where this is the identity. *)
Hypothesis HRO : forall a, (exists r, In r LBraid.REAC_BRAID_ENCODE_RO_RD /\ fst r <= a < fst r + snd r) ->
  crtA_in_ro_rd RO_RD a.

Lemma crtA_segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr).
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin).
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; unfold kLowMemEnd; lia|]). destruct H.
Qed.

Lemma crtA_aview_vis : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff segs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma crtA_aview_mrd : forall (W : world segs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma crtA_aview_some : forall (W : world segs) mem a v, aview segs (w_H W) mem a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ exists b : byte, mrd rsegs mem (wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem a v H. pose proof (crtA_aview_vis W mem a v H) as Hv. split; [exact Hv|].
  rewrite (crtA_aview_mrd W mem a Hv) in H.
  destruct (mrd rsegs mem (wa a)) as [b|] eqn:E; [|discriminate H]. exists b. split; [reflexivity|].
  injection H as H. exact H.
Qed.

Lemma crtA_present_eq : forall (W : world segs) m m' a,
  apresent (w_H W) m a -> apresent (w_H W) m' a -> aview segs (w_H W) m' a = aview segs (w_H W) m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' a (Hh & b & Hb) (_ & b' & Hb') E.
  rewrite (crtA_aview_mrd W m' a Hh), (crtA_aview_mrd W m a Hh) in E. unfold mrd, wa in E.
  rewrite Hb, Hb' in E. cbn in E. injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma crtA_rw_cells_ext : forall m m' A cs,
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (A + i)) = m (wa (A + i))) ->
  rw_cells rsegs m A cs -> rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs E [[Hwf (H0 & Hl & Hb)] (W0 & W1 & Hw)].
  pose proof (cells_bytes_length cs Hwf) as Lc.
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hb i Hi). unfold mrd.
    rewrite (E (Z.of_nat i)) by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (Hw i Hi). unfold wview in *.
    rewrite (E i Hi). exact Hw.
Qed.

Lemma crtA_req_size : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma crtA_nodup : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
  induction l as [|x t IH]; intros Hpos Hp; [apply List.NoDup_nil|]. cbn in Hp. destruct Hp as [HF Hp].
  apply List.NoDup_cons; [|apply IH; [intros b Hb; apply Hpos; right; exact Hb | exact Hp]].
  intros Hin.
  pose proof (proj1 (Forall_forall _ _) HF (fst x, req_size (snd x))
    (in_map (fun b => (fst b, req_size (snd b))) t x Hin)) as Hd.
  pose proof (Hpos x (or_introl eq_refl)) as H0.
  unfold zdisjoint, req_size in Hd. cbn in Hd. destruct (Z.eqb_spec (snd x) 0); lia.
Qed.

(* The three temporaries of crtA_blocks3 are blocks of the cut state, the caller's blocks are kept, the again
   block R is new (not a caller block), and R is a different block from Q and from P. *)
Lemma crtA_blk3 : forall lyc Sc ly1 S1 (W1 : world segs) mem1 md1 P Q R nch ns,
  AR segs B ly1 S1 W1 mem1 md1 ->
  Permutation (ablocks B ly1 S1)
    ((R, 3 * (nch * ns)) :: (Q, 8 * nch) :: (P, 4 * (nch * ns)) :: ablocks B lyc Sc) ->
  In (R, 3 * (nch * ns)) (ablocks B ly1 S1) /\ In (Q, 8 * nch) (ablocks B ly1 S1) /\
  In (P, 4 * (nch * ns)) (ablocks B ly1 S1) /\
  (forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly1 S1)) /\
  ~ In (R, 3 * (nch * ns)) (ablocks B lyc Sc) /\
  (R, 3 * (nch * ns)) <> (Q, 8 * nch) /\ (R, 3 * (nch * ns)) <> (P, 4 * (nch * ns)).
Proof.
  intros lyc Sc ly1 S1 W1 mem1 md1 P Q R nch ns HAR1 Hp.
  assert (Hin : forall b, In b ((R, 3 * (nch * ns)) :: (Q, 8 * nch) :: (P, 4 * (nch * ns)) :: ablocks B lyc Sc) ->
                  In b (ablocks B ly1 S1))
    by (intros b Hb; exact (Permutation_in b (Permutation_sym Hp) Hb)).
  pose proof (Hin _ (or_introl eq_refl)) as HinR.
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 R (3 * (nch * ns)) HAR1 HinR) as (_ & _ & _ & _ & _ & Hpw & _).
  assert (Hpos : forall b, In b (ablocks B ly1 S1) -> 0 <= snd b).
  { intros [p n] Hb. destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 p n HAR1 Hb) as (_ & _ & _ & _ & _ & _ & H0).
    cbn. lia. }
  pose proof (Permutation_NoDup Hp (crtA_nodup _ Hpos Hpw)) as ND.
  apply List.NoDup_cons_iff in ND as [N1 _].
  split; [exact HinR|]. split; [apply Hin; right; left; reflexivity|].
  split; [apply Hin; right; right; left; reflexivity|].
  split; [intros b Hb; apply Hin; right; right; right; exact Hb|].
  split; [intros H; apply N1; right; right; exact H|].
  split; intros E; apply N1; [left; exact (eq_sym E) | right; left; exact (eq_sym E)].
Qed.

(* RNG_W W holds on a range of bytes the world does not hide. *)
Lemma crtA_rng : forall (W : world segs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (unsigned_lit b) by lia. apply H. lia.
Qed.

(* A byte of a loaded segment is never hidden (YK04.v:38 H_off_segments). *)
Lemma crtA_vis_seg : forall (W : world segs) a,
  (exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a (sg & Hin & Hr). destruct (w_H W (Z_to_bv 64 a)) eqn:E; [exfalso|reflexivity].
  pose proof (@w_Hoff segs W _ E) as F.
  assert (Ha : 0 <= a < kLowMemEnd) by (apply crtA_segs_low; exists sg; split; [exact Hin | exact Hr]).
  rewrite (unsigned_lit a) in F by (unfold kLowMemEnd in Ha; lia).
  exact (crt_find_none segs a 1 sg F Hin ltac:(lia) ltac:(lia)).
Qed.

(* The shadow hull a block gives (shadow_hull_vis) is not hidden. *)
Lemma crtA_vis_hull : forall (W : world segs) mem x n s,
  shadow_hull_vis (aview segs (w_H W) mem) x n ->
  YG0f.shadow_addr x / 8 * 8 <= s < YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  w_H W (Z_to_bv 64 s) = false.
Proof.
  intros W mem x n s H Hs. specialize (H s Hs).
  destruct (aview segs (w_H W) mem s) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (crtA_aview_vis W mem s v E).
Qed.

Lemma crtA_byte_signed : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (byte_range b) as R. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

(* decode's addressable (AsanCells.v:27) from cgif's range_addressable (YG0v) over a range of application memory. *)
Lemma crtA_addressable : forall (W : world segs) mem p n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n -> 0 <= n ->
  4096 <= p /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p /\ p + n <= ASAN_CEIL) ->
  addressable mem p n.
Proof.
  intros W mem p n HA Hn Happ. pose proof ASAN_CEIL_range as [CR _].
  split; [lia|]. split; [exact Hn|]. split; [unfold APPMEM_END, kLowShadowBeg, kHighMemBeg in *; lia|].
  intros i Hi. split.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, kLowShadowBeg, kHighMemBeg in *. lia.
  - destruct (HA (p + i) ltac:(lia)) as (s & Hs & Hok).
    destruct (crtA_aview_some W mem _ s Hs) as (_ & b & Hb & Eb).
    exists b. split.
    + replace (AsanCells.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
        by (unfold AsanCells.shadow_addr, shadow_of_addr, ASAN_K, SHADOW_OFF; lia).
      exact Hb.
    + pose proof (byte_range b) as R. unfold saddr_ok in Hok. unfold shadow_ok.
      rewrite crtA_byte_signed by lia. lia.
Qed.

(* cgif's view of the caller's memory is decode's mrd of the restricted overlay. *)
Lemma crtA_rd_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  aview segs H m a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs (mrestrict H m) (wa a)).
Proof. reflexivity. Qed.

(* The braid relation of the statement (dec_crt_braid, over cgif's view) is check_braid_c's braid_map over the
   restricted overlay. *)
Lemma crtA_braid_map : forall (H : word -> bool) (memc : word -> option byte) audio pcm nch ns,
  dec_crt_braid (aview segs H memc) audio pcm nch ns -> braid_map (mrestrict H memc) audio pcm nch ns.
Proof.
  intros H memc audio pcm nch ns HB ch s j Hch Hs Hj.
  destruct (HB ch s j Hch Hs Hj) as (v & H1 & H2).
  rewrite crtA_rd_mrd in H1, H2.
  destruct (mrd rsegs (mrestrict H memc) (wa (pcm + 3 * (ch * ns + s) + j))) as [b1|] eqn:E1; [|discriminate H1].
  destruct (mrd rsegs (mrestrict H memc) (wa (audio + 3 * (s * nch + 2 * (ch / 2)) + DCBc.braid_off ch j)))
    as [b2|] eqn:E2; [|discriminate H2].
  injection H1 as H1. injection H2 as H2.
  assert (Eb : b2 = b1) by (apply bv_eq; lia). subst b2.
  exists b1. split; reflexivity.
Qed.

Lemma crtA_pb_rd : forall (H : word -> bool) (memc : word -> option byte) pcm i,
  crtA_pb (aview segs H memc) pcm i = bv_unsigned (crt_rd (mrestrict H memc) pcm i).
Proof.
  intros H memc pcm i. unfold crtA_pb, crt_rd. rewrite crtA_rd_mrd.
  destruct (mrd rsegs (mrestrict H memc) (wa (pcm + i))); reflexivity.
Qed.

(* The float the convert loop leaves for sample (ch, s) is f32 of the 24-bit sample crt_K reads. *)
Lemma crtA_cv_K : forall (H : word -> bool) (memc : word -> option byte) pcm ns s ch,
  crtA_cv (aview segs H memc) pcm (ch * ns + s) = f32 (crt_K (crt_rd (mrestrict H memc) pcm) ns s ch) (-23).
Proof.
  intros H memc pcm ns s ch. unfold crtA_cv, crtA_s24, crt_K, s24. rewrite !crtA_pb_rd. reflexivity.
Qed.

Lemma crtA_s24_range : forall b0 b1 b2 : byte, - 2 ^ 23 <= s24 b0 b1 b2 < 2 ^ 23.
Proof.
  intros b0 b1 b2. pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
  unfold s24. destruct (Z.leb_spec 128 (bv_unsigned b2)); lia.
Qed.

Lemma crtA_le4 : forall v, le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
  intros v. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z_to_le_bytes_mod. lia.
Qed.

(* The prologue's frame is kept by every memory that agrees with the old one on its 96 bytes. *)
Lemma crtA_frame_ext : forall regs m m',
  (forall i, 0 <= i < CRT_FRAME -> m' (wa (spZ regs - CRT_FRAME + i)) = m (wa (spZ regs - CRT_FRAME + i))) ->
  crtA_frame regs m -> crtA_frame regs m'.
Proof.
  intros regs m m' E H. unfold crtA_frame in *. eapply crtA_rw_cells_ext; [|exact H].
  intros i Hi. apply E. cbn in Hi. unfold CRT_FRAME. lia.
Qed.

Lemma crtA_in_rom_img : forall a, in_rom segs a -> in_img segs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

Lemma crtA_encode_at : CRT_ENCODE = REAC_BRAID_ENCODE.
Proof. vm_compute. reflexivity. Qed.

(* A range dec_seg_covers accepts lies in a loaded segment. *)
Lemma crtA_covers_img : forall a n x, dec_seg_covers a n = true -> a <= x < a + n ->
  exists sg, In sg segs /\ Z.of_N (seg_base sg) <= x < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  intros a n x H Hx. unfold dec_seg_covers in H. apply existsb_exists in H as (sg & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.

Lemma crtA_shadow_addr_eq : forall a, AsanCells.shadow_addr a = YG0f.shadow_addr a.
Proof. intros a. unfold AsanCells.shadow_addr, YG0f.shadow_addr, ASAN_K, SHADOW_OFF. lia. Qed.

(* RNG_W W holds on the 8-aligned shadow cover of a block range whose shadow the block law makes visible. *)
Lemma crtA_rng_hull : forall (W : world segs) mem x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 48 ->
  shadow_hull_vis (aview segs (w_H W) mem) x n ->
  rng (LCK.RNG_W (world segs) (@w_H segs) W) (AsanCells.shadow_addr x / 8 * 8)
    (AsanCells.shadow_addr (x + n - 1) / 8 * 8 + 8 - AsanCells.shadow_addr x / 8 * 8).
Proof.
  intros W mem x n H0 Hn H1 H. rewrite !crtA_shadow_addr_eq.
  assert (B1 : 0 <= YG0f.shadow_addr x / 8 * 8) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  assert (B2 : YG0f.shadow_addr x / 8 * 8 <= YG0f.shadow_addr (x + n - 1) / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (B3 : YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 64) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  apply crtA_rng; [exact B1 | lia |]. intros s Hs. apply (crtA_vis_hull W mem x n s H). lia.
Qed.

Lemma crtA_present_vis : forall (W : world segs) m a, apresent (w_H W) m a -> aview segs (w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (crtA_aview_mrd W m a Hh). unfold mrd, wa. rewrite Hb. discriminate.
Qed.

(* Every byte the braid encoder writes lies in its output range. *)
Lemma crtA_rows_in : forall a N K f e, 2 <= N -> N mod 2 = 0 -> In e (rb_rows a N K f) ->
  a <= fst e < a + 3 * N * Z.of_nat f.
Proof.
  intros a N K f. induction f as [|f IH]; intros e HN HE H; cbn [rb_rows] in H; [destruct H|].
  apply in_app_or in H as [H|H].
  - specialize (IH e HN HE H). lia.
  - destruct (rb_row_in _ _ _ _ _ _ H) as (c & j & Hc & Hj & E). rewrite E.
    rewrite Z2Nat.id in Hc by lia. rewrite rb_at_eq by lia.
    pose proof (rb_off_rng (c mod 2) j ltac:(lia)) as Ho.
    assert (Hc2 : 2 * (c / 2) <= N - 2) by lia.
    nia.
Qed.

(* A range one read-only segment holds is read-only image data (in_rom), decided on the segment list. *)
Lemma crtA_rom_range : forall b n a,
  existsb (fun sg : Segment => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? b) &&
                               (b + n <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool segs = true ->
  b <= a < b + n -> in_rom segs a.
Proof.
  intros b n a H Ha. apply existsb_exists in H as (sg & Hin & Hb).
  apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [Hw H1].
  apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin|]. split; [exact Hw | lia].
Qed.

(* The view rom_view-type agreement on a read-only byte is decode's: mrd of the overlay is the image byte. *)
Lemma crtA_ro_mrd : forall (W : world segs) mem a,
  in_rom segs a ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) ->
  mrd rsegs mem (wa a) = seg_rom rsegs (wa a).
Proof.
  intros W mem a Hrom E.
  assert (Hh : w_H W (Z_to_bv 64 a) = false)
    by (apply crtA_vis_seg; destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  rewrite (crtA_aview_mrd W mem a Hh) in E.
  change (seg_rom segs (Z_to_bv 64 a)) with (seg_rom rsegs (wa a)) in E.
  destruct (mrd rsegs mem (wa a)) as [b1|]; destruct (seg_rom rsegs (wa a)) as [b2|];
    cbn [option_map] in E; try discriminate E.
  - injection E as E. f_equal. apply bv_eq. exact E.
  - reflexivity.
Qed.

Theorem crtA_enc_piece : crtA_at_bcmp B MT RO_RD -> crtA_at_loopout B MT RO_RD.
Proof.
  intros HB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
    ly1 S1 W1 mem1 md1 regs1 P Q R fx1 Hpre Hmid Hregs Hblk Hfrm Hconv.
  pose proof Hpre as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hev
    & Hnch & Hns & Hreg & HbA & HbA1 & HbA2 & HbP & HbP1 & HbP2 & Hbraid & Hnev & Hlive & Hmo & Hcost
    & Htm & Htf & Hufix & Hrom0 & Hsc).
  pose proof Hmid as (HJ & Hfrs & Hmole & Hfr & Hrom1).
  pose proof Hregs as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs3 & Rs4 & Rs5 & Rs7 & Rs8 & Rs11).
  pose proof Hblk as (Hperm & HP0 & HQ0 & HR0).
  pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & Hkeep & _ & _ & _ & Hpres & Hstk & _ & HQT).
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  pose proof (@ASAN_CEIL_range rc) as [Hcr _]. unfold ASAN_CEIL in Hcr.
  assert (Hsp : YM05.alloc_ceiling + 16480 <= spZ regs <= 2 ^ 47)
    by (unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hslo; lia).
  assert (Hnn : 2 <= nch * ns) by nia.
  assert (En : 3 * nch * ns = 3 * (nch * ns)) by ring.
  (* the three temporaries and the caller's audio block, at the cut state *)
  destruct (crtA_blk3 lyc Sc ly1 S1 W1 mem1 md1 P Q R nch ns HAR1 Hperm)
    as (HinR & HinQ & HinP & Hsub & HnR & HneRQ & HneRP).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 R _ HAR1 HinR) as (_ & _ & HRc & HRapp & HRb & _ & _).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 Q _ HAR1 HinQ) as (HQ16 & _ & HQc & HQapp & HQb & _ & _).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 P _ HAR1 HinP) as (HP16 & _ & HPc & HPapp & HPb & _ & _).
  rewrite crtA_req_size in HRc, HRapp, HRb by lia.
  rewrite crtA_req_size in HQc, HQapp, HQb by lia.
  rewrite crtA_req_size in HPc, HPapp, HPb by lia.
  pose proof (sep_blocks segs B LAWS ly1 S1 W1 mem1 md1 _ _ _ _ HAR1 HinR HinQ HneRQ) as DRQ.
  pose proof (sep_blocks segs B LAWS ly1 S1 W1 mem1 md1 _ _ _ _ HAR1 HinR HinP HneRP) as DRP.
  rewrite !crtA_req_size in DRQ, DRP by lia. unfold zdisjoint in DRQ, DRP. cbn [fst snd] in DRQ, DRP.
  pose proof (Hsub _ HbA) as HinA.
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 bA nA HAR1 HinA) as (_ & HA4 & HAc & HAapp & HAb & _ & _).
  rewrite crtA_req_size in HAc, HAapp, HAb by lia.
  (* ---- +0x1f0 .. +0x204: the arguments of reac_braid_encode (crt_seg5_F) ---- *)
  eapply (@crtA_run fx1 W1 regs1 mem1 md1 CRT_LOOP_OUT).
  { unfold LCK.ms_of_regs. apply crt_seg5_F. }
  intros msE mdE (ms0 & E0 & HeqE) HsbE. subst ms0.
  pose proof (@crtA_ms_shape fx1 _ _ _ msE HeqE) as EmsE.
  set (regsE := ms_regs msE) in *.
  assert (REcs : forall r, acallee_saved r -> YKK.getr regsE (Z_to_bv 5 r) = YKK.getr regs1 (Z_to_bv 5 r)).
  { intros r Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
    unfold regsE.
    repeat (destruct Hc as [->|Hc]; [rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity; reflexivity|]).
    subst r. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity. reflexivity. }
  assert (RE1 : YKK.getr regsE (Z_to_bv 5 1) = Z_to_bv 64 (CRT_AT 0x208))
    by (unfold regsE; rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity; reflexivity).
  assert (RE10 : YKK.getr regsE (Z_to_bv 5 10) = w64 R).
  { unfold regsE. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity.
    transitivity (YKK.getr regs1 (Z_to_bv 5 23)); [reflexivity | exact Rs7]. }
  assert (RE11 : YKK.getr regsE (Z_to_bv 5 11) = w64 nch).
  { unfold regsE. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity.
    transitivity (YKK.getr regs1 (Z_to_bv 5 19)); [reflexivity | exact Rs3]. }
  assert (RE12 : YKK.getr regsE (Z_to_bv 5 12) = w64 Q).
  { unfold regsE. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity.
    transitivity (YKK.getr regs1 (Z_to_bv 5 21)); [reflexivity | exact Rs5]. }
  assert (RE13 : YKK.getr regsE (Z_to_bv 5 13) = w64 nch).
  { unfold regsE. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity.
    transitivity (YKK.getr regs1 (Z_to_bv 5 19)); [reflexivity | exact Rs3]. }
  assert (RE14 : YKK.getr regsE (Z_to_bv 5 14) = w64 ns).
  { unfold regsE. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqE) by reflexivity.
    transitivity (YKK.getr regs1 (Z_to_bv 5 18)); [reflexivity | exact Rs2]. }
  assert (HspE : spZ regsE = spZ regs - CRT_FRAME).
  { transitivity (bv_unsigned (YKK.getr regsE (Z_to_bv 5 2))); [reflexivity|].
    rewrite (REcs 2) by (unfold acallee_saved; lia).
    transitivity (bv_unsigned (w64 (spZ regs - CRT_FRAME))); [f_equal; exact Rsp|].
    unfold w64, CRT_FRAME. apply unsigned_lit. lia. }
  (* the journal at the materialized model of the run *)
  assert (HJE : @ajournal rc dec_A_sink_head segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 mdE 3).
  { apply (@ajournal_exec rc dec_A_sink_head segs B LAWS crtA_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem1 mdE
             (fun _ => False) HJ); [intros; reflexivity | intros x Hx; exact Hx | intros; reflexivity |
             exact HsbE | intros a []]. }
  assert (HECE : ecall_pre segs B ly1 S1 W1 regsE mem1 mdE).
  { apply (@ecall_pre_at rc dec_A_sink_head segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1
             mem1 mdE 3 regsE (- CRT_FRAME) HJE).
    - rewrite HspE. lia.
    - reflexivity.
    - unfold CRT_FRAME. lia.
    - unfold ESTACK, CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK. lia.
    - change (YKK.getr regsE 1) with (YKK.getr regsE (Z_to_bv 5 1)). rewrite RE1. apply ret_ok_even.
      rewrite unsigned_lit by (vm_compute; split; congruence). vm_compute. reflexivity.
    - change (YKK.getr regsE 3) with (YKK.getr regsE (Z_to_bv 5 3)).
      rewrite (REcs 3) by (unfold acallee_saved; lia). exact (eq_trans Rgp Hgp).
    - change (YKK.getr regsE 4) with (YKK.getr regsE (Z_to_bv 5 4)).
      rewrite (REcs 4) by (unfold acallee_saved; lia). exact (eq_trans Rtp Htp). }
  pose proof HECE as (HARE & HraE & Hal16E & HloE & HhiE & HpresE & HgpE & HtpE).
  pose proof (@w_Hoff segs W1) as HoffW1.
  (* ---- the call of reac_braid_encode (its leaf contract, dec_reac_braid_encode_cg) ---- *)
  rewrite EmsE, crtA_encode_at.
  eapply SRr_bind.
  { apply (ALEAF fx1 ly1 S1 W1 regsE mem1 mdE R nch Q ns (fun ch => P + 4 * (ch * ns))
             (fun s ch => crtA_cv (aview segs (w_H W) memc) pcm (ch * ns + s))
             (crt_K (crt_rd (mrestrict (w_H W) memc) pcm) ns));
      cbv beta;
      try (replace (bv_unsigned (YKK.getr regsE (Z_to_bv 5 2))) with (spZ regs - CRT_FRAME)
             by (symmetry; exact HspE));
      try (unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME).
    - exact HECE.
    - exact RE10.
    - exact RE11.
    - exact RE12.
    - exact RE13.
    - exact RE14.
    - exact Hnch.
    - rewrite Zmod_even, Hev. reflexivity.
    - exact Hns.
    - exact Hfrm.
    - (* the leaf's read-only reads see the image bytes: crtA_rom_on of the cut *)
      intros a Ha. pose proof (HRO (bv_unsigned a) Ha) as Hin.
      assert (Hrom : in_rom segs (bv_unsigned a)).
      { destruct Ha as (r0 & Hr0 & Hrr). unfold LBraid.REAC_BRAID_ENCODE_RO_RD in Hr0.
        repeat (destruct Hr0 as [<-|Hr0]; [refine (crtA_rom_range _ _ _ _ Hrr); vm_compute; reflexivity|]).
        destruct Hr0. }
      replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned).
      exact (crtA_ro_mrd W1 mem1 (bv_unsigned a) Hrom (Hrom1 (bv_unsigned a) Hin Hrom)).
    - (* the leaf's frame is off those bytes (stack above the image) *)
      intros x Hx. cbn [outside]. split; [|exact I].
      assert (Hrom : in_rom segs x).
      { destruct Hx as (r0 & Hr0 & Hrx). unfold LBraid.REAC_BRAID_ENCODE_RO_RD in Hr0.
        repeat (destruct Hr0 as [<-|Hr0]; [refine (crtA_rom_range _ _ _ _ Hrx); vm_compute; reflexivity|]).
        destruct Hr0. }
      pose proof (crtA_segs_low x (crtA_in_rom_img x Hrom)) as Hlow. unfold kLowMemEnd in Hlow. lia.
    - (* the leaf's 48-byte frame is present stack *)
      unfold stk. split; [unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME; lia|]. split; [lia|].
      intros a Ha.
      destruct (HpresE a ltac:(rewrite HspE; unfold ESTACK, CRT_FRAME, REAC_BRAID_ENCODE_FRAME in *; lia))
        as (_ & b & Hb).
      unfold wview, mrd, wa. rewrite Hb. split; [discriminate | exists b; reflexivity].
    - lia.
    - rewrite En. lia.
    - split; [lia|]. split; [rewrite En; lia|]. intros i Hi.
      destruct (HRb (R + i) ltac:(rewrite En in Hi; lia)) as ((_ & b & Hb) & _).
      unfold wview, wa. rewrite Hb. discriminate.
    - lia.
    - lia.
    - lia.
    - exact (proj1 Hconv).
    - intros c Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia.
      split; [lia|]. split; [|lia].
      replace (P + 4 * (c * ns)) with ((4 * (P / 16) + c * ns) * 4) by lia. apply Z.mod_mul. lia.
    - intros s c Hs Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia. split.
      + pose proof (proj2 Hconv (c * ns + s) ltac:(lia)) as Hb. rewrite crtA_le4.
        replace (P + 4 * (c * ns) + 4 * s) with (P + 4 * (c * ns + s)) by ring. exact Hb.
      + split; [unfold crt_K; apply crtA_s24_range | left; apply crtA_cv_K].
    - rewrite En. exact DRQ.
    - intros c Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia. rewrite En. lia.
    - left. rewrite En. unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME. lia.
    - left. unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME. lia.
    - intros c Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia.
      left. unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME. lia.
    - exact (dec_cells_asan B HCELLS ly1 S1 W1 mem1 mdE HoffW1 HARE).
    - rewrite En. apply (crtA_addressable W1 mem1 R (3 * (nch * ns))).
      + apply (range_addressable_of_block segs B LAWS ly1 S1 W1 mem1 mdE R (3 * (nch * ns)));
          [exact HARE | exact HinR | lia | rewrite crtA_req_size by lia; lia].
      + lia.
      + exact HRapp.
    - apply (crtA_addressable W1 mem1 Q (8 * nch)).
      + apply (range_addressable_of_block segs B LAWS ly1 S1 W1 mem1 mdE Q (8 * nch));
          [exact HARE | exact HinQ | lia | rewrite crtA_req_size by lia; lia].
      + lia.
      + exact HQapp.
    - intros c Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia.
      apply (crtA_addressable W1 mem1 (P + 4 * (c * ns)) (4 * ns)).
      + apply (range_addressable_of_block segs B LAWS ly1 S1 W1 mem1 mdE P (4 * (nch * ns)));
          [exact HARE | exact HinP | lia | rewrite crtA_req_size by lia; lia].
      + lia.
      + destruct HPapp as [HPa1 [HPa2|HPa2]]; split; [lia | left; lia | lia | right; lia].
    - (* the runtime cells and the shadow lie off the leaf's frame and off the again block *)
      intros x Hx. cbn [outside].
      assert (Hxs : x < HIGHMEM_BEG)
        by (unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia).
      split; [unfold HIGHMEM_BEG, CRT_FRAME, REAC_BRAID_ENCODE_FRAME in *; lia|]. split; [|exact I].
      intros HxR. rewrite En in HxR.
      assert (HnoR : ~ in_img segs x).
      { destruct (al_client_img _ _ LAWS ly1 S1 W1 mem1 md1 x HAR1) as [_ Hni]; [|exact Hni].
        left. exists R, (3 * (nch * ns)). split; [exact HinR | rewrite crtA_req_size by lia; lia]. }
      destruct Hx as [Hx|[Hx|Hx]].
      + apply HnoR. apply (crtA_covers_img GOT_CELL_K 8 x); [vm_compute; reflexivity | exact Hx].
      + apply HnoR. apply (crtA_covers_img CELL_K 8 x); [vm_compute; reflexivity | exact Hx].
      + unfold in_app in HRapp.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, kLowShadowBeg, kHighMemBeg in *.
        lia.
    - apply crtA_rng; [unfold GOT_CELL_K; lia | unfold GOT_CELL_K; lia |]. intros b Hb.
      apply crtA_vis_seg. exact (crtA_covers_img GOT_CELL_K 8 b ltac:(vm_compute; reflexivity) Hb).
    - apply crtA_rng; [unfold CELL_K; lia | unfold CELL_K; lia |]. intros b Hb.
      apply crtA_vis_seg. exact (crtA_covers_img CELL_K 8 b ltac:(vm_compute; reflexivity) Hb).
    - apply crtA_rng; [lia | lia |]. intros b Hb. apply crtA_vis_seg.
      assert (Hrom : in_rom segs b) by (refine (crtA_rom_range _ _ _ _ Hb); vm_compute; reflexivity).
      destruct Hrom as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr].
    - apply crtA_rng; [unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME; lia | lia |]. intros b Hb.
      destruct (HpresE b ltac:(rewrite HspE; unfold ESTACK, CRT_FRAME, REAC_BRAID_ENCODE_FRAME in *; lia))
        as (Hh & _). exact Hh.
    - apply crtA_rng; [lia | rewrite En; lia |]. intros b Hb. rewrite En in Hb. exact (proj1 (proj1 (HRb b Hb))).
    - rewrite En. apply (crtA_rng_hull W1 mem1); [lia | lia | lia |].
      apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem1 mdE R (3 * (nch * ns)));
        [exact HARE | exact HinR | lia | rewrite crtA_req_size by lia; lia | lia].
    - apply crtA_rng; [lia | lia |]. intros b Hb. exact (proj1 (proj1 (HQb b Hb))).
    - apply (crtA_rng_hull W1 mem1); [lia | lia | lia |].
      apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem1 mdE Q (8 * nch));
        [exact HARE | exact HinQ | lia | rewrite crtA_req_size by lia; lia | lia].
    - intros c Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia.
      apply crtA_rng; [lia | lia |]. intros b Hb. exact (proj1 (proj1 (HPb b ltac:(lia)))).
    - intros c Hc0. assert (c * ns + ns <= nch * ns) by nia. assert (0 <= c * ns) by nia.
      apply (crtA_rng_hull W1 mem1); [lia | lia | lia |].
      apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem1 mdE P (4 * (nch * ns)));
        [exact HARE | exact HinP | lia | rewrite crtA_req_size by lia; lia | lia].
    - intros x Hx. unfold LCK.in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [|apply Exists_nil in Hx; destruct Hx]. cbn [fst snd] in Hx. rewrite En in Hx.
      split; [exact (proj2 (HRb x Hx))|].
      destruct (al_client_img _ _ LAWS ly1 S1 W1 mem1 md1 x HAR1) as [_ Hni]; [|exact Hni].
      left. exists R, (3 * (nch * ns)). split; [exact HinR | rewrite crtA_req_size by lia; lia]. }
  (* ---- the return of reac_braid_encode at +0x208 ---- *)
  intros W' c' _ (-> & fx' & regs2 & mem2 & md2 & -> & Hcsr & _ & HAR2 & Hpres2 & Hsb2 & Hview2 & Happ2 & HX).
  assert (R2cs : forall r, acallee_saved r -> YKK.getr regs2 (Z_to_bv 5 r) = YKK.getr regs1 (Z_to_bv 5 r))
    by (intros r Hr; exact (eq_trans (Hpres2 r Hr) (REcs r Hr))).
  set (Wr2 := fun a => spZ regs - CRT_FRAME - ESTACK <= a < spZ regs - CRT_FRAME \/ R <= a < R + 3 * (nch * ns)).
  assert (HJ2 : @ajournal rc dec_A_sink_head segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem2 md2 3).
  { apply (@ajournal_after_write rc dec_A_sink_head segs B LAWS crtA_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             mem2 md2 Wr2 S1 [] HJE).
    - intros a Ha HnW. apply Hview2; [exact Ha | |].
      + change (LCK.spZ regsE) with (spZ regsE). rewrite HspE. intros Hw. apply HnW. left. exact Hw.
      + intros Hin. unfold LCK.in_wr in Hin. apply Exists_cons in Hin.
        destruct Hin as [Hin|Hin]; [|apply Exists_nil in Hin; destruct Hin]. cbn [fst snd] in Hin.
        apply HnW. right. rewrite <- En. exact Hin.
    - exact Happ2.
    - exact Hsb2.
    - intros a [Ha|Ha]; left.
      + left. unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK, CRT_FRAME, ESTACK in *. lia.
      + right. right. left. exists R, (3 * (nch * ns)).
        split; [exact HinR|]. split; [exact HnR | rewrite crtA_req_size by lia; lia].
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - cbn [app]. exact Hfrs.
    - exact HQT. }
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeep2 & _ & _ & _ & Hpres2j & _ & _ & _).
  (* ---- +0x208 .. +0x214: the arguments of bcmp (crt_seg6_F) ---- *)
  assert (EraE : LCK.w64 (LCK.raZ regsE) = Z_to_bv 64 (CRT_AT 0x208)).
  { unfold LCK.w64, LCK.raZ. rewrite RE1. rewrite unsigned_lit by (vm_compute; split; congruence). reflexivity. }
  rewrite EraE.
  eapply (@crtA_run fx' W1 regs2 mem2 md2 (CRT_AT 0x208)).
  { unfold LCK.ms_of_regs. apply crt_seg6_F. }
  intros msT mdT (ms0 & E0 & HeqT) HsbT. subst ms0.
  pose proof (@crtA_ms_shape fx' _ _ _ msT HeqT) as EmsT.
  set (regsT := ms_regs msT) in *.
  assert (RTcs : forall r, acallee_saved r -> YKK.getr regsT (Z_to_bv 5 r) = YKK.getr regs1 (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (R2cs r Hr).
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
    unfold regsT.
    repeat (destruct Hc as [->|Hc]; [rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqT) by reflexivity; reflexivity|]).
    subst r. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqT) by reflexivity. reflexivity. }
  assert (RT1 : YKK.getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (CRT_AT 0x218))
    by (unfold regsT; rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqT) by reflexivity; reflexivity).
  assert (RT10 : YKK.getr regsT (Z_to_bv 5 10) = w64 R).
  { unfold regsT. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqT) by reflexivity.
    transitivity (YKK.getr regs2 (Z_to_bv 5 23)); [reflexivity|].
    rewrite (R2cs 23) by (unfold acallee_saved; lia). exact Rs7. }
  assert (RT11 : YKK.getr regsT (Z_to_bv 5 11) = w64 audio).
  { unfold regsT. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqT) by reflexivity.
    transitivity (YKK.getr regs2 (Z_to_bv 5 9)); [reflexivity|].
    rewrite (R2cs 9) by (unfold acallee_saved; lia). exact Rs1. }
  assert (RT12 : YKK.getr regsT (Z_to_bv 5 12) = w64 (3 * (nch * ns))).
  { unfold regsT. rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ HeqT) by reflexivity.
    transitivity (YKK.getr regs2 (Z_to_bv 5 20)); [reflexivity|].
    rewrite (R2cs 20) by (unfold acallee_saved; lia). exact Rs4. }
  assert (HspT : spZ regsT = spZ regs - CRT_FRAME).
  { transitivity (bv_unsigned (YKK.getr regsT (Z_to_bv 5 2))); [reflexivity|].
    rewrite (RTcs 2) by (unfold acallee_saved; lia).
    transitivity (bv_unsigned (w64 (spZ regs - CRT_FRAME))); [f_equal; exact Rsp|].
    unfold w64, CRT_FRAME. apply unsigned_lit. lia. }
  assert (HJT : @ajournal rc dec_A_sink_head segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem2 mdT 3).
  { apply (@ajournal_exec rc dec_A_sink_head segs B LAWS crtA_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 mdT
             (fun _ => False) HJ2); [intros; reflexivity | intros x Hx; exact Hx | intros; reflexivity |
             exact HsbT | intros a []]. }
  (* the bytes bcmp compares: the encoded rows at R are the caller's audio *)
  pose proof (crtA_braid_map (w_H W) memc audio pcm nch ns Hbraid) as BM.
  assert (Hnch2 : nch mod 2 = 0) by (rewrite Zmod_even, Hev; reflexivity).
  assert (Heq : forall i, 0 <= i < 3 * (nch * ns) ->
            aview segs (w_H W1) mem2 (R + i) = aview segs (w_H W1) mem2 (audio + i)).
  { intros i Hi.
    destruct (HRb (R + i) ltac:(lia)) as ((HhR & _) & _).
    rewrite (crtA_aview_mrd W1 mem2 (R + i) HhR). unfold mrd at 1.
    rewrite HX.
    2:{ cbn [outside]. rewrite wa_unsigned by lia.
        change (bv_unsigned (YKK.getr regsE (Z_to_bv 5 2))) with (spZ regsE). rewrite HspE.
        unfold CRT_FRAME, REAC_BRAID_ENCODE_FRAME. split; [lia | exact I]. }
    rewrite (crt_out (mrestrict (w_H W) memc) mem1 R audio pcm nch ns ltac:(lia) Hnch2 ltac:(lia)
               ltac:(lia) ltac:(rewrite En; lia) BM i ltac:(rewrite En; lia)).
    replace (audio + i) with (bA + (audio + i - bA)) by ring.
    rewrite (Hkeep2 bA nA (audio + i - bA) HbA HinA ltac:(rewrite crtA_req_size by lia; lia)
               ltac:(intros (r & Hr & _); destruct Hr)).
    replace (bA + (audio + i - bA)) with (audio + i) by ring.
    rewrite crtA_rd_mrd.
    rewrite (crt_audio_ok (mrestrict (w_H W) memc) audio pcm nch ns ltac:(lia) Hnch2 ltac:(lia) BM i
               ltac:(rewrite En; lia)).
    reflexivity. }
  (* ---- the call of bcmp (abcmp_realizes, in the journal form YCbq.v:2062 aj_bcmp_at) ---- *)
  rewrite EmsT.
  eapply SRr_bind.
  { apply (@aj_bcmp_at fx' rc dec_A_sink_head segs B LAWS crtA_segs_low
             (decode_sigma DS___interceptor_trampoline_bcmp) (ABCMP fx') W1 regsT mem2 DEC_CRT_STK (spZ regs) []
             lyc Sc W memc mdc [] ly1 S1 mdT 3 R audio (3 * (nch * ns)) (- CRT_FRAME)
             (Z_to_bv 64 (CRT_AT 0x218)) HJT).
    - exact RT10.
    - exact RT11.
    - exact RT12.
    - rewrite En in Hreg. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HspT. lia.
    - reflexivity.
    - unfold CRT_FRAME. lia.
    - unfold ESTACK, CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK. lia.
    - change (YKK.getr regsT 3) with (YKK.getr regsT (Z_to_bv 5 3)).
      rewrite (RTcs 3) by (unfold acallee_saved; lia). exact (eq_trans Rgp Hgp).
    - change (YKK.getr regsT 4) with (YKK.getr regsT (Z_to_bv 5 4)).
      rewrite (RTcs 4) by (unfold acallee_saved; lia). exact (eq_trans Rtp Htp).
    - exact RT1.
    - apply ret_ok_even. rewrite unsigned_lit by (vm_compute; split; congruence). vm_compute. reflexivity.
    - intros a Ha. split.
      + apply crtA_present_vis. apply Happ2. exact (proj1 (HRb a ltac:(lia))).
      + rewrite HspT. unfold ESTACK, CRT_FRAME. lia.
    - intros a Ha. split.
      + apply crtA_present_vis. apply Happ2. exact (proj1 (HAb a ltac:(lia))).
      + rewrite HspT. unfold ESTACK, CRT_FRAME. lia.
    - intros a Ha. unfold ESTACK, CRT_FRAME. lia.
    - intros a Ha. unfold ESTACK, CRT_FRAME. lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 mem2 md2 R (3 * (nch * ns))); 
        [exact HAR2 | exact HinR | lia | rewrite crtA_req_size by lia; lia].
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 mem2 md2 bA nA);
        [exact HAR2 | exact HinA | lia | rewrite crtA_req_size by lia; lia].
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 mem2 md2 R (3 * (nch * ns)));
        [exact HAR2 | exact HinR | lia | rewrite crtA_req_size by lia; lia].
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem2 md2 R (3 * (nch * ns)));
        [exact HAR2 | exact HinR | lia | rewrite crtA_req_size by lia; lia | lia].
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 mem2 md2 bA nA);
        [exact HAR2 | exact HinA | lia | rewrite crtA_req_size by lia; lia].
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 mem2 md2 bA nA);
        [exact HAR2 | exact HinA | lia | rewrite crtA_req_size by lia; lia | lia]. }
  (* ---- the cut after bcmp, at CRT_RET_BCMP: crtA_at_bcmp ---- *)
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & Hpres3 & Hv & Hiff & Hview3 & Happ3).
  assert (R3cs : forall r, acallee_saved r -> YKK.getr regs3 (Z_to_bv 5 r) = YKK.getr regs1 (Z_to_bv 5 r))
    by (intros r Hr; exact (eq_trans (Hpres3 r Hr) (RTcs r Hr))).
  apply (HB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
           ly1 S1 W1 mem3 md3 regs3 P Q R fx' Hpre).
  - (* crtA_mid at the cut *)
    split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hmole|]. split.
    + apply (crtA_frame_ext regs mem1 mem3); [|exact Hfr]. intros i Hi.
      unfold CRT_FRAME in Hi. set (a := spZ regs - CRT_FRAME + i).
      assert (Ha2 : apresent (w_H W1) mem2 a)
        by (apply Hpres2j; unfold a, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK, CRT_FRAME; lia).
      unfold wa. rewrite (crtA_present_eq W1 mem2 mem3 a Ha2 (Happ3 a Ha2)
                            (Hview3 a ltac:(unfold a, CRT_FRAME; lia)
                               ltac:(unfold a, ESTACK, CRT_FRAME; lia))).
      change (Z_to_bv 64 a) with (wa a). rewrite HX.
      * apply rb_enc_notin. intros e He.
        pose proof (crtA_rows_in R nch _ _ e ltac:(lia) Hnch2 He) as Hb.
        rewrite Z2Nat.id in Hb by lia. rewrite wa_unsigned by (unfold a, CRT_FRAME; lia).
        unfold a, CRT_FRAME. lia.
      * cbn [outside]. rewrite wa_unsigned by (unfold a, CRT_FRAME; lia).
        change (bv_unsigned (YKK.getr regsE (Z_to_bv 5 2))) with (spZ regsE). rewrite HspE.
        unfold a, CRT_FRAME, REAC_BRAID_ENCODE_FRAME. split; [lia | exact I].
    + intros a Hro Hrom. pose proof (crtA_segs_low a (crtA_in_rom_img a Hrom)) as Hlow.
      rewrite (Hview3 a ltac:(unfold kLowMemEnd in Hlow; lia) ltac:(unfold ESTACK, CRT_FRAME, kLowMemEnd in *; lia)).
      rewrite (Hview2 a ltac:(unfold kLowMemEnd in Hlow; lia)).
      * exact (Hrom1 a Hro Hrom).
      * change (LCK.spZ regsE) with (spZ regsE). rewrite HspE. unfold LCK.ESTACK, CRT_FRAME, kLowMemEnd in *. lia.
      * intros Hin. unfold LCK.in_wr in Hin. apply Exists_cons in Hin.
        destruct Hin as [Hin|Hin]; [|apply Exists_nil in Hin; destruct Hin]. cbn [fst snd] in Hin.
        destruct (al_client_img _ _ LAWS ly1 S1 W1 mem1 md1 a HAR1) as [_ Hni];
          [|exact (Hni (crtA_in_rom_img a Hrom))].
        left. exists R, (3 * (nch * ns)). split; [exact HinR | rewrite crtA_req_size by lia; lia].
  - (* crtA_regs at the cut *)
    unfold crtA_regs.
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 2)); [exact (R3cs 2 ltac:(unfold acallee_saved; lia)) | exact Rsp]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 3)); [exact (R3cs 3 ltac:(unfold acallee_saved; lia)) | exact Rgp]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 4)); [exact (R3cs 4 ltac:(unfold acallee_saved; lia)) | exact Rtp]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 8)); [exact (R3cs 8 ltac:(unfold acallee_saved; lia)) | exact Rs0]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 9)); [exact (R3cs 9 ltac:(unfold acallee_saved; lia)) | exact Rs1]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 18)); [exact (R3cs 18 ltac:(unfold acallee_saved; lia)) | exact Rs2]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 19)); [exact (R3cs 19 ltac:(unfold acallee_saved; lia)) | exact Rs3]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 20)); [exact (R3cs 20 ltac:(unfold acallee_saved; lia)) | exact Rs4]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 21)); [exact (R3cs 21 ltac:(unfold acallee_saved; lia)) | exact Rs5]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 23)); [exact (R3cs 23 ltac:(unfold acallee_saved; lia)) | exact Rs7]|].
    split; [transitivity (YKK.getr regs1 (Z_to_bv 5 24)); [exact (R3cs 24 ltac:(unfold acallee_saved; lia)) | exact Rs8]|].
    transitivity (YKK.getr regs1 (Z_to_bv 5 27)); [exact (R3cs 27 ltac:(unfold acallee_saved; lia)) | exact Rs11].
  - (* bcmp answered 0 *)
    transitivity v; [exact Hv | apply Hiff; exact Heq].
  - exact Hblk.
  - rewrite Hcsr. exact Hfrm.
Qed.

End CrtEncW.

(* HRO at the statement's read-only set: REAC_BRAID_ENCODE_RO_RD is contained in DEC_RO_RD
   (check_round_trip_cg.v), decided on the two lists, so it stays proved while DEC_RO_RD grows. *)
Lemma crtA_ro_sub : forall L D : list (Z * Z),
  forallb (fun r => existsb (fun d => (fst d <=? fst r) && (fst r + snd r <=? fst d + snd d))%bool D) L = true ->
  forall a, (exists r, In r L /\ fst r <= a < fst r + snd r) -> crtA_in_ro_rd D a.
Proof.
  intros L D H a (r & Hr & Ha). rewrite forallb_forall in H. specialize (H r Hr).
  apply existsb_exists in H as (d & Hd & Hb). apply andb_true_iff in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists d. split; [exact Hd | lia].
Qed.

Lemma crtA_leaf_ro_in_dec : forall a,
  (exists r, In r LBraid.REAC_BRAID_ENCODE_RO_RD /\ fst r <= a < fst r + snd r) -> crtA_in_ro_rd DEC_RO_RD a.
Proof. apply crtA_ro_sub. vm_compute. reflexivity. Qed.

(* The piece at the statement's read-only set, HRO discharged by crtA_leaf_ro_in_dec. *)
Theorem crtA_enc_piece_dec {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall fx' : YKK.FPState, @abcmp_realizes fx' rc decodesegs0 B (decode_sigma DS___interceptor_trampoline_bcmp)) ->
  (forall fx' : YKK.FPState, @dec_leaf_wr_at rc B (@LBraid.dec_reac_braid_encode_cg) fx') ->
  crtA_at_bcmp B MT DEC_RO_RD -> crtA_at_loopout B MT DEC_RO_RD.
Proof.
  intros HL HCl HBc HLf. exact (@crtA_enc_piece rc B MT DEC_RO_RD HL HCl HBc HLf crtA_leaf_ro_in_dec).
Qed.

