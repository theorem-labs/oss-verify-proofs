(* diginet_frame_build_kit (image B): the helpers of lib/B/Prog/diginet_frame_build_walk.v that are not facts of one state of
   the walk:
   - fbk_regs_of: the registers of a footprint run's final state, read off its mkR form;
   - the image view read as bytes: a visible byte's view is its footprint byte (fbk_aview_mrd), bytes_at and garr8
     as pointwise views and back, a view kept outside a munch range;
   - fbk_rng_shadow: the shadow bytes of a range [q, q + n), one footprint range when each is visible;
   - fbk_put_nth, fbk_frame_bytes: the cap bytes at out the function leaves, written as windows (iface fb_put), are
     DgnSpec.build_frame and then the old tail. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0f YG0v YG0n YG0d YI04 YI00 YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame Cells Step ExecF PropExec Regs6ss MState.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Img0 AsanCells YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit diginet_frame_build_iface.
Import ListNotations.
Open Scope Z_scope.
Module FBI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_iface.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Lemma fbk_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply MState.unsigned_lit. lia. Qed.

(* ---- the registers of a run's final state ---- *)

Lemma fbk_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {R' : bvmap 5 word},
  Regs6ss.xregs_eqv (LFrame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       x24 x25 x26 x27 x28 x29 x30 x31) R' ->
  YK11.getr R' (Z_to_bv 5 1) = x1 /\ YK11.getr R' (Z_to_bv 5 2) = x2 /\ YK11.getr R' (Z_to_bv 5 3) = x3 /\
  YK11.getr R' (Z_to_bv 5 4) = x4 /\ YK11.getr R' (Z_to_bv 5 8) = x8 /\ YK11.getr R' (Z_to_bv 5 9) = x9 /\
  YK11.getr R' (Z_to_bv 5 10) = x10 /\ YK11.getr R' (Z_to_bv 5 11) = x11 /\ YK11.getr R' (Z_to_bv 5 12) = x12 /\
  YK11.getr R' (Z_to_bv 5 18) = x18 /\ YK11.getr R' (Z_to_bv 5 19) = x19 /\ YK11.getr R' (Z_to_bv 5 20) = x20 /\
  YK11.getr R' (Z_to_bv 5 21) = x21 /\ YK11.getr R' (Z_to_bv 5 22) = x22 /\ YK11.getr R' (Z_to_bv 5 23) = x23 /\
  YK11.getr R' (Z_to_bv 5 24) = x24 /\ YK11.getr R' (Z_to_bv 5 25) = x25 /\ YK11.getr R' (Z_to_bv 5 26) = x26 /\
  YK11.getr R' (Z_to_bv 5 27) = x27.
Proof.
  intros until R'. intros H.
  repeat split; (etransitivity; [apply (decode_getr_xeqv _ _ H) | reflexivity]).
Qed.

(* ---- the image view ---- *)

Lemma fbk_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v E. destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. exfalso.
  pose proof (w_Hoff W _ Eh) as F.
  unfold aview, mbyte, mrestrict in E. rewrite Eh in E.
  unfold YK11.seg_rom, memory_read in E. cbn [Z.of_N] in E. rewrite F in E. discriminate E.
Qed.

Lemma fbk_aview_mrd : forall (H : word -> bool) mem a, H (Z_to_bv 64 a) = false ->
  aview tfibsegs H mem a = option_map (fun b : byte => bv_unsigned b) (LMem.mrd BImg0.rsegs mem (LMem.wa a)).
Proof. intros H mem a Ha. unfold aview. rewrite decode_mbyte_vis by exact Ha. reflexivity. Qed.

Lemma fbk_aview_of_bytes : forall (H : word -> bool) mem A (l : list byte),
  LMem.bytes_at BImg0.rsegs mem A l ->
  (forall j, (j < length l)%nat -> H (Z_to_bv 64 (A + Z.of_nat j)) = false) ->
  forall j, (j < length l)%nat -> aview tfibsegs H mem (A + Z.of_nat j) = Some (bz (nth j l (b8 0))).
Proof.
  intros H mem A l (_ & _ & Hb) Hv j Hj. rewrite fbk_aview_mrd by exact (Hv j Hj).
  rewrite (Hb j Hj).
  assert (E : nth_error l j = Some (nth j l (b8 0))) by (apply nth_error_nth'; exact Hj).
  rewrite E. reflexivity.
Qed.

Lemma fbk_bytes_of_aview : forall (W : world tfibsegs) mem A (l : list byte),
  0 <= A -> A + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, (j < length l)%nat -> aview tfibsegs (w_H W) mem (A + Z.of_nat j) = Some (bz (nth j l (b8 0)))) ->
  LMem.bytes_at BImg0.rsegs mem A l.
Proof.
  intros W mem A l H0 H1 HA. split; [exact H0|]. split; [exact H1|].
  intros j Hj. specialize (HA j Hj).
  pose proof (fbk_aview_vis W mem _ _ HA) as Hv.
  rewrite fbk_aview_mrd in HA by exact Hv.
  assert (E : nth_error l j = Some (nth j l (b8 0))) by (apply nth_error_nth'; exact Hj). rewrite E.
  destruct (LMem.mrd BImg0.rsegs mem (LMem.wa (A + Z.of_nat j))) as [b|]; cbn in HA; [|discriminate].
  injection HA as HA. f_equal. apply bv_eq. exact HA.
Qed.

Lemma fbk_garr8_aview : forall (H : word -> bool) mem A (l : list byte),
  0 <= A -> A + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, (j < length l)%nat -> H (Z_to_bv 64 (A + Z.of_nat j)) = false) ->
  garr8 tfibsegs (mrestrict H mem) A (map bz l) ->
  forall j, (j < length l)%nat -> aview tfibsegs H mem (A + Z.of_nat j) = Some (bz (nth j l (b8 0))).
Proof.
  intros H mem A l H0 H1 Hv G. apply fbk_aview_of_bytes; [|exact Hv].
  exact (decode_garr8_bytes H mem A l H0 H1 Hv G).
Qed.

Lemma fbk_aview_garr8 : forall (W : world tfibsegs) mem A (l : list byte),
  0 <= A -> A + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, (j < length l)%nat -> aview tfibsegs (w_H W) mem (A + Z.of_nat j) = Some (bz (nth j l (b8 0)))) ->
  garr8 tfibsegs (mrestrict (w_H W) mem) A (map bz l).
Proof.
  intros W mem A l H0 H1 HA. apply decode_bytes_garr8.
  - intros j Hj. exact (fbk_aview_vis W mem _ _ (HA j Hj)).
  - exact (fbk_bytes_of_aview W mem A l H0 H1 HA).
Qed.

(* A byte outside the range a run writes keeps its view. *)
Lemma fbk_aview_munch : forall (H : word -> bool) (m m' : word -> option byte) lo hi a,
  LFrame.munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
  intros H m m' lo hi a MU Ha Hn. unfold aview, mbyte, mrestrict.
  rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  cbn [LFrame.outside]. rewrite fbk_u64 by exact Ha. split; [exact Hn | exact I].
Qed.

Lemma fbk_raw_munch : forall (m m' : word -> option byte) lo hi a,
  LFrame.munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m' (LMem.wa a) = m (LMem.wa a).
Proof.
  intros m m' lo hi a MU Ha Hn. apply MU. cbn [LFrame.outside]. unfold LMem.wa. rewrite fbk_u64 by exact Ha.
  split; [exact Hn | exact I].
Qed.

(* ---- the shadow bytes of a range ---- *)

Lemma fbk_shadow_cover : forall q n s, 0 < n ->
  FC.shadow_addr q <= s <= FC.shadow_addr (q + n - 1) -> exists j, 0 <= j < n /\ FC.shadow_addr (q + j) = s.
Proof.
  intros q n s Hn Hs. unfold FC.shadow_addr in *.
  set (t := s - FC.ASAN_K).
  assert (Ht : q / 8 <= t <= (q + n - 1) / 8) by (unfold t; lia).
  destruct (Z_le_gt_dec (8 * t - q) 0) as [Hle | Hgt].
  - exists 0. split; [lia|]. rewrite Z.add_0_r.
    assert (q / 8 = t) by (Z.div_mod_to_equations; lia). unfold t in *. lia.
  - exists (8 * t - q). split.
    + split; [lia|]. Z.div_mod_to_equations. lia.
    + replace (q + (8 * t - q)) with (t * 8) by lia. rewrite Z.div_mul by lia. unfold t. lia.
Qed.

Lemma fbk_rng_shadow : forall (W : world tfibsegs) q n, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (FC.shadow_addr (q + i))) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (FC.shadow_addr q)
    (FC.shadow_addr (q + n - 1) - FC.shadow_addr q + 1).
Proof.
  intros W q n H0 Hn H1 Hv.
  assert (Hm : q / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (Hb : (q + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (Hq : 0 <= q / 8) by (apply Z.div_pos; lia).
  apply decode_rng_vis.
  - unfold FC.shadow_addr, FC.ASAN_K. lia.
  - unfold FC.shadow_addr, FC.ASAN_K. lia.
  - intros i Hi. destruct (fbk_shadow_cover q n (FC.shadow_addr q + i) Hn) as (j & Hj & E); [lia|].
    rewrite <- E. exact (Hv j Hj).
Qed.

(* ---- the bytes at out ---- *)

Lemma fbk_put_nth : forall (l w : list byte) k j d, (k + length w <= length l)%nat -> (j < length l)%nat ->
  nth j (FBI.fb_put l k w) d =
  if (j <? k)%nat then nth j l d else if (j <? k + length w)%nat then nth (j - k) w d else nth j l d.
Proof.
  intros l w k j d Hk Hj. unfold FBI.fb_put.
  destruct (Nat.ltb_spec j k) as [H1|H1].
  - rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
    destruct (Nat.ltb_spec j k); [reflexivity | lia].
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Nat.min k (length l)) with k by lia.
    destruct (Nat.ltb_spec j (k + length w)) as [H2|H2].
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma fbk_put_nil : forall (l : list byte) k, (k <= length l)%nat -> FBI.fb_put l k [] = l.
Proof. intros l k H. unfold FBI.fb_put. cbn [app length]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Lemma fbk_put_app : forall (l : list byte) k k' w1 w2, k' = (k + length w1)%nat ->
  (k + length w1 + length w2 <= length l)%nat ->
  FBI.fb_put (FBI.fb_put l k w1) k' w2 = FBI.fb_put l k (w1 ++ w2).
Proof. intros l k k' w1 w2 -> H. apply FBI.fb_put_app. exact H. Qed.

(* The sum field: mode 0 stores diginet_sum16's result, the 16 low bits of the body's sum, as spec_sum does; mode 1
   stores 0. *)
Lemma fbk_sum_field : forall (bb : list byte) mode, mode = 0 \/ mode = 1 ->
  put16 (FBI.fb_sum bb mode) = put16 (if mode =? 1 then 0 else spec_sum bb).
Proof.
  intros bb mode [-> | ->]; unfold FBI.fb_sum; cbn [Z.eqb].
  - rewrite lib_sum16_eq, spec_sum_eq. reflexivity.
  - reflexivity.
Qed.

(* The windows the function writes, in order, give build_frame and the old tail after it. *)
Lemma fbk_frame_bytes : forall (oj dmac smac bb : list byte) send ack retry cmd ncmds mode,
  length dmac = 6%nat -> length smac = 6%nat -> (mode = 0 \/ mode = 1) ->
  frame_len (length bb) <= Z.of_nat (length oj) ->
  FBI.fb_put (FBI.fb_put (FBI.fb_put (FBI.fb_put (FBI.fb_put (FBI.fb_put (FBI.fb_put oj 0 dmac) 6 smac)
      12 (put16 0x885f ++ put16 (16 + Z.of_nat (length bb)))) 16 (put16 (FBI.fb_sum bb mode) ++ put32 send))
      22 (put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds])) 30 bb) (30 + length bb) (repeat (b8 0) (30 - length bb))
  = build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1) ++
    skipn (length (build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1))) oj.
Proof.
  intros oj dmac smac bb send ack retry cmd ncmds mode Hd Hs Hm Hcap.
  unfold frame_len in Hcap.
  assert (L1 : length (put16 0x885f ++ put16 (16 + Z.of_nat (length bb))) = 4%nat) by reflexivity.
  assert (L2 : length (put16 (FBI.fb_sum bb mode) ++ put32 send) = 6%nat) by reflexivity.
  assert (L3 : length (put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]) = 8%nat) by reflexivity.
  assert (Lz : length (repeat (b8 0) (30 - length bb)) = (30 - length bb)%nat) by apply repeat_length.
  remember (put16 0x885f ++ put16 (16 + Z.of_nat (length bb))) as h1 eqn:Eh1.
  remember (put16 (FBI.fb_sum bb mode) ++ put32 send) as h2 eqn:Eh2.
  remember (put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]) as h3 eqn:Eh3.
  remember (repeat (b8 0) (30 - length bb)) as z eqn:Ez.
  rewrite (fbk_put_app oj 0 6 dmac smac) by lia.
  rewrite (fbk_put_app oj 0 12 (dmac ++ smac) h1) by (rewrite ?length_app; lia).
  rewrite (fbk_put_app oj 0 16 ((dmac ++ smac) ++ h1) h2) by (rewrite ?length_app; lia).
  rewrite (fbk_put_app oj 0 22 (((dmac ++ smac) ++ h1) ++ h2) h3) by (rewrite ?length_app; lia).
  rewrite (fbk_put_app oj 0 30 ((((dmac ++ smac) ++ h1) ++ h2) ++ h3) bb) by (rewrite ?length_app; lia).
  rewrite (fbk_put_app oj 0 (30 + length bb) (((((dmac ++ smac) ++ h1) ++ h2) ++ h3) ++ bb) z)
    by (rewrite ?length_app; lia).
  unfold FBI.fb_put. cbn [firstn app Nat.add].
  assert (EF : (((((dmac ++ smac) ++ h1) ++ h2) ++ h3) ++ bb) ++ z =
               build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1)).
  { subst h1 h2 h3 z. unfold build_frame. rewrite <- (fbk_sum_field bb mode Hm).
    repeat rewrite <- app_assoc. reflexivity. }
  rewrite EF. reflexivity.
Qed.
