(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: adapted from reac-repacer/fuzz_uci's lib/A/Prog/rp_uci_int_cgW.v for reac-repacer/fuzz_wire's rp_copy_untag in image A: its glue lemmas (rui_ -> wcu_) and its form of the walk copied; the model lemmas, the two callee calls and the post written for this function. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/rp_copy_untag_cgW.v, with its module paths, module names, addresses and numbers changed; 310 of its 942 lines of code are new or changed and 163 lines of the source are left out. *)
(* rp_copy_untag_cgW: the proof of lib/B/Prog/rp_copy_untag_cg.v's frozen wire_rp_copy_untag_holds_stmt, for every
   float state, run ceiling and record B. The walk is the cgif-form walk of reac-repacer/fuzz_uci's
   lib/B/Prog/rp_uci_int_cgW.v, as this unit's image-A twin lib/A/Prog/rp_copy_untag_cgW.v walks the same function:
   the function's own code runs as footprint runs (lib/B/Prog/rp_copy_untag_cgW_runs.v), each carried into SRr by the
   leaf kit's bridge (lib/B/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n) after the state transport of
   lib/B/Prog/LeafCgGlue.v; the three calls are cut by the statement's premises: is_tagged_reac
   (lib/B/Prog/is_tagged_reac_cg.v) and reac_frame_is_reac (lib/B/Prog/reac_frame_is_reac_cg.v), each through
   lib/B/Prog/WireCg.v wire_leaf_at, and the checked memmove (lib/B/Rt/MemmoveDef.v amemmove_realizes).
   - n < 50: rcu_seg_small runs to the return (a0 = 0); its frame write keeps AR (wcu_mem_post: the frame is in the
     stack, so no owned byte, and present, so no hidden byte).
   - n >= 50: rcu_seg_call_tag writes the frame, reads the shadow base through its GOT word and calls
     is_tagged_reac (f), whose premises are the statement's frame premises read through the frame write; its result
     is is_tagged_result bs. rcu_seg_tag_ret then goes, by that result, to the checked memmove (f + 12, f + 16,
     n - 16) or straight to reac_frame_is_reac. With the move, the memmove's post gives the moved bytes (the OLD
     bytes of f + 16 ..) and keeps every byte outside [f + 12, f + n - 4) and its stack window; rcu_seg_mm_ret runs
     to reac_frame_is_reac (f, n - 4).
     wcu_tail: the leaf call (its premises from the views: the frame holds cu_bytes n bs, its shadow bytes and the
     runtime cells are the entry's), then rcu_seg_leaf_ret reads f[16], f[17] after the leaf (which writes only its
     stack window) and returns; the result is copy_untag_result n bs (wcu_result).
   The footprint of every run is LeafCgKit.v RNG_W W (the visible bytes); each byte a run reads is visible: the
   function's frame by the stack premise, the runtime cells by their views, f's bytes and their shadow bytes by
   their views. The UBSan branches to `unimp` are refuted inside the runs by 0 < f and f + n <= 2 ^ 63, the two
   branches into the error path by the shadow bytes (range_addressable). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import MState Mem Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Regs6ss ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00 YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c YK1b YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg rp_copy_untag_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WireCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require AsanKA reac_frame_is_reac_c reac_frame_is_reac_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require is_tagged_reac_F_c is_tagged_reac_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_copy_untag_cgW_runs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgGlue.
Module LB := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WireCcLeafb.
Module KA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
Module LRc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_is_reac_c.
Module LIR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_is_reac_cg.
Module LTc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_F_c.
Module LIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_cg.
Module RR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_copy_untag_cgW_runs.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.
Module UC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Module I0 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Img0.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the model: the frame after the call and the result (lib/Prog/rp_copy_untag_c.v) ---- *)

Lemma wcu_byte_nth : forall (l : list byte) i, (i < length l)%nat ->
  nth_error l i = Some (nth i l (Z_to_bv 8 0)).
Proof. intros l i Hi. apply nth_error_nth'. exact Hi. Qed.

(* With the tag, byte i of cu_bytes is byte i + 4 of bs on [12, n - 4), else byte i of bs. *)
Lemma wcu_cu_bytes_tag : forall n (bs : list byte) i,
  PRc.cu_tagged bs = true -> 50 <= n -> Z.of_nat (length bs) = n -> 0 <= i < n ->
  PRc.cu_byte (PRc.cu_bytes n bs) (Z.to_nat i) =
    (if (12 <=? i) && (i <? n - 4) then PRc.cu_byte bs (Z.to_nat (i + 4)) else PRc.cu_byte bs (Z.to_nat i))%bool.
Proof.
  intros n bs i T Hn Hl Hi.
  assert (MV : PRc.cu_moves n bs = true)
    by (unfold PRc.cu_moves; rewrite T, (proj2 (Z.leb_le 50 n) Hn); reflexivity).
  unfold PRc.cu_bytes. rewrite MV.
  set (mv := firstn (Z.to_nat (n - 16)) (skipn 16 bs)).
  assert (Lmv : length mv = Z.to_nat (n - 16)) by (unfold mv; rewrite length_firstn, length_skipn; lia).
  assert (LU : length (upd_bytes bs 12 mv) = length bs) by (apply upd_bytes_length; lia).
  unfold PRc.cu_byte.
  assert (E : nth_error (upd_bytes bs 12 mv) (Z.to_nat i) =
              if (Nat.leb 12 (Z.to_nat i) && Nat.ltb (Z.to_nat i) (12 + length mv))%bool
              then nth_error mv (Z.to_nat i - 12) else nth_error bs (Z.to_nat i))
    by (apply upd_bytes_nth; lia).
  rewrite (wcu_byte_nth (upd_bytes bs 12 mv) (Z.to_nat i)) in E by lia.
  destruct (Z.leb_spec 12 i) as [H1|H1]; destruct (Z.ltb_spec i (n - 4)) as [H2|H2]; cbn [andb].
  - rewrite (proj2 (Nat.leb_le 12 (Z.to_nat i))) in E by lia.
    rewrite (proj2 (Nat.ltb_lt (Z.to_nat i) (12 + length mv))) in E by lia. cbn [andb] in E.
    unfold mv in *. rewrite nth_error_firstn in E.
    rewrite (proj2 (Nat.ltb_lt (Z.to_nat i - 12) (Z.to_nat (n - 16)))) in E by lia.
    rewrite nth_error_skipn in E.
    rewrite (wcu_byte_nth bs (16 + (Z.to_nat i - 12))) in E by lia.
    injection E as E. rewrite E. f_equal. f_equal. lia.
  - rewrite (proj2 (Nat.leb_le 12 (Z.to_nat i))) in E by lia.
    rewrite (proj2 (Nat.ltb_ge (Z.to_nat i) (12 + length mv))) in E by lia. cbn [andb] in E.
    rewrite (wcu_byte_nth bs (Z.to_nat i)) in E by lia. injection E as E. rewrite E. reflexivity.
  - rewrite (proj2 (Nat.leb_gt 12 (Z.to_nat i))) in E by lia. cbn [andb] in E.
    rewrite (wcu_byte_nth bs (Z.to_nat i)) in E by lia. injection E as E. rewrite E. reflexivity.
  - rewrite (proj2 (Nat.leb_gt 12 (Z.to_nat i))) in E by lia. cbn [andb] in E.
    rewrite (wcu_byte_nth bs (Z.to_nat i)) in E by lia. injection E as E. rewrite E. reflexivity.
Qed.

Lemma wcu_cu_bytes_notag : forall n (bs : list byte), PRc.cu_tagged bs = false -> PRc.cu_bytes n bs = bs.
Proof. intros n bs T. unfold PRc.cu_bytes, PRc.cu_moves. rewrite T, andb_false_r. reflexivity. Qed.

Lemma wcu_cu_bytes_length : forall n (bs : list byte), Z.of_nat (length bs) = n ->
  length (PRc.cu_bytes n bs) = length bs.
Proof.
  intros n bs Hl. unfold PRc.cu_bytes. destruct (PRc.cu_moves n bs) eqn:MV; [|reflexivity].
  unfold PRc.cu_moves in MV. apply andb_true_iff in MV as [MV _]. apply Z.leb_le in MV.
  apply upd_bytes_length. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma wcu_cu_len : forall n (bs : list byte), 50 <= n ->
  PRc.cu_len n bs = if PRc.cu_tagged bs then n - 4 else n.
Proof.
  intros n bs Hn. unfold PRc.cu_len, PRc.cu_moves. rewrite (proj2 (Z.leb_le 50 n) Hn). reflexivity.
Qed.

(* The value the code returns (rcu_seg_leaf_ret, from the leaf's result r and the bytes 16, 17 of the frame after
   the move) is copy_untag_result. *)
Lemma wcu_result : forall f n (bs : list byte),
  f <> 0 -> 50 <= n ->
  (if LRc.is_reac_result f (PRc.cu_len n bs) (PRc.cu_bytes n bs) =? 0 then 0
   else if (bv_unsigned (nth 16 (PRc.cu_bytes n bs) (Z_to_bv 8 0)) =? 0) &&
           (bv_unsigned (nth 17 (PRc.cu_bytes n bs) (Z_to_bv 8 0)) =? 0)
        then PRc.cu_len n bs else 0)%bool = PRc.copy_untag_result n bs.
Proof.
  intros f n bs Hf Hn.
  assert (HL : 14 <= PRc.cu_len n bs) by (rewrite wcu_cu_len by lia; destruct (PRc.cu_tagged bs); lia).
  unfold LRc.is_reac_result, PRc.copy_untag_result, LRc.is_reac_byte, PRc.cu_byte.
  rewrite (proj2 (Z.eqb_neq f 0) Hf), (proj2 (Z.ltb_ge _ 14) HL), (proj2 (Z.ltb_ge n 50) Hn). cbn [orb].
  set (b12 := bv_unsigned (nth 12 (PRc.cu_bytes n bs) (Z_to_bv 8 0))).
  set (b13 := bv_unsigned (nth 13 (PRc.cu_bytes n bs) (Z_to_bv 8 0))).
  set (b16 := bv_unsigned (nth 16 (PRc.cu_bytes n bs) (Z_to_bv 8 0))).
  set (b17 := bv_unsigned (nth 17 (PRc.cu_bytes n bs) (Z_to_bv 8 0))).
  destruct (b12 =? 0x88), (b13 =? 0x19), (b16 =? 0), (b17 =? 0); reflexivity.
Qed.

Lemma wcu_reac_01 : forall f L (bs : list byte), LRc.is_reac_result f L bs = 0 \/ LRc.is_reac_result f L bs = 1.
Proof.
  intros f L bs. unfold LRc.is_reac_result.
  destruct ((f =? 0) || (L <? 14))%bool; [left; reflexivity|].
  destruct ((LRc.is_reac_byte bs 12 =? 0x88) && (LRc.is_reac_byte bs 13 =? 0x19))%bool; [right | left]; reflexivity.
Qed.

Lemma wcu_tag_01 : forall (bs : list byte), LTc.is_tagged_result bs = 0 \/ LTc.is_tagged_result bs = 1.
Proof. intros bs. unfold LTc.is_tagged_result. destruct (PRc.cu_tagged bs); [right | left]; reflexivity. Qed.

(* ---- facts of the walk that name no state of this function ---- *)

(* The frame's shadow bytes lie in [0x7fff8000, 0x10007fff8000): below every stack address (layout_ok lo_top) and
   outside the frame itself (amem_range puts the frame below 0x7fff8000 or at or above 0x10007fff8000). *)
Lemma wcu_shadow_off : forall f n x, amem_range f n -> 0 <= f -> f <= x < f + n ->
  0x7fff8000 <= shadow_of_addr SHADOW_OFF x < 0x10007fff8000 /\
  (shadow_of_addr SHADOW_OFF x < f \/ f + n <= shadow_of_addr SHADOW_OFF x).
Proof.
  intros f n x HA H0 Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Lemma wcu_hull_off : forall f n a k s, amem_range f n -> 0 <= f -> f <= a -> 0 < k -> a + k <= f + n ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + k - 1) / 8 * 8 + 8 ->
  0x7fff8000 <= s < 0x10007fff8000 /\ (s < f \/ f + n <= s).
Proof.
  intros f n a k s HA H0 Ha Hk Hak Hs. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold shadow_addr, SHADOW_OFF in Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma wcu_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128. Z.div_mod_to_equations. lia.
Qed.

(* rw_cells is a property of the bytes of its range only *)
Lemma wcu_rw_cells_eq : forall (m m' : word -> option byte) A cs,
  rw_cells I0.rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (A + i)) = m (wa (A + i))) ->
  rw_cells I0.rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf [H0 [H1 Hb]]] [W0 [W1 Hw]]] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (Hb i Hi). unfold mrd. rewrite (E (Z.of_nat i)); [reflexivity|]. rewrite L in Hi. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    unfold wview. rewrite (E i Hi). exact (Hw i Hi).
Qed.

Section Glue.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.

(* Hidden bytes are off the image (YA0n.v w_Hoff), so a byte with a view is not hidden. *)
Lemma wcu_vis : forall (W : world segs) mem x, aview segs (w_H W) mem x <> None -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W mem x H. destruct (w_H W (Z_to_bv 64 x)) eqn:E; [|reflexivity]. exfalso. apply H.
  assert (R : YK11.seg_rom segs (Z_to_bv 64 x) = None).
  { pose proof (w_Hoff W _ E) as Hf. unfold YK11.seg_rom, memory_read.
    rewrite (Hf : find_segment segs (bv_unsigned (Z_to_bv 64 x)) (Z.of_N 1) = None). reflexivity. }
  unfold aview, YP09.mbyte, mrestrict. rewrite E. cbv beta iota. rewrite R. reflexivity.
Qed.

(* A byte with a view is read by the machine at its value. *)
Lemma wcu_mrd : forall (W : world segs) mem x v, aview segs (w_H W) mem x = Some v ->
  exists b, mrd I0.rsegs mem (wa x) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem x v H.
  assert (E : w_H W (Z_to_bv 64 x) = false) by (apply (wcu_vis W mem x); rewrite H; discriminate).
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H. cbv beta iota in H.
  unfold mrd, wa. revert H.
  destruct (mem (Z_to_bv 64 x)) as [b|] eqn:Hm; intros H.
  - cbn in H. injection H as <-. exists b. split; reflexivity.
  - revert H. destruct (YK11.seg_rom segs (Z_to_bv 64 x)) as [b|] eqn:Hs; intros H; cbn in H; [|discriminate].
    injection H as <-. exists b. split; [exact Hs | reflexivity].
Qed.

Lemma wcu_mrd_eq : forall (W : world segs) mem x (b : byte), aview segs (w_H W) mem x = Some (bv_unsigned b) ->
  mrd I0.rsegs mem (wa x) = Some b.
Proof.
  intros W mem x b H. destruct (wcu_mrd W mem x _ H) as (b' & Hb' & Hu). rewrite Hb'. f_equal. apply bv_eq. exact Hu.
Qed.

(* Two present bytes with the same view are the same byte. *)
Lemma wcu_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  apresent H m a -> apresent H' m' a -> aview segs H' m' a = aview segs H m a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E. rewrite Hh, Hh', Hb, Hb' in E. cbn in E. injection E as E.
  rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

(* A range of visible bytes is in the walk's footprint. *)
Lemma wcu_rng_vis : forall (W : world segs) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LK.RNG_W (world segs) (@w_H segs) W) a n.
Proof.
  intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj. unfold LK.RNG_W, LK.range_avoids. intros kk Hk. unfold LK.woff.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

(* An 8-byte constant cell of the record, read through its view, is the machine's le8 bytes. *)
Lemma wcu_cell8 : forall (W : world segs) mem a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall k, (k < 8)%nat -> aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v 8 k)) ->
  (forall k, (k < 8)%nat -> exists b, nth_error (le8 (wa v)) k = Some b /\ bv_unsigned b = le_byte v 8 k) ->
  bytes_at I0.rsegs mem a (le8 (wa v)).
Proof.
  intros W mem a v H0 H8 HV HN. split; [lia|]. split; [rewrite length_le8; cbn; lia|].
  intros i Hi. rewrite length_le8 in Hi. destruct (HN i Hi) as (b0 & Hb0 & Hu0). rewrite Hb0.
  destruct (wcu_mrd W mem (a + Z.of_nat i) _ (HV i Hi)) as (b & Hb & Hu).
  rewrite Hb. f_equal. apply bv_eq. rewrite Hu, Hu0. reflexivity.
Qed.

(* The frame byte j, from garr8, read through its view. *)
Lemma wcu_frame_view : forall (W : world segs) mem r (bs : list byte) j,
  garr8 segs (mrestrict (w_H W) mem) r (map (fun b : byte => bv_unsigned b) bs) -> (j < length bs)%nat ->
  aview segs (w_H W) mem (r + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
  intros W mem r bs j HG Hj.
  assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
  assert (Em : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hj'.
    exact (map_nth (fun b : byte => bv_unsigned b) bs (Z_to_bv 8 0) j). }
  destruct (HG j Hj') as (HV & HR). specialize (HV 0%nat ltac:(lia)).
  change (Z.of_nat 0) with 0 in HV. rewrite Z.add_0_r in HV.
  unfold aview. rewrite HV. cbn [option_map]. f_equal. rewrite <- Em.
  assert (S0 : forall z, Z.shiftr z (8 * Z.of_nat 0) = z) by (intros z; reflexivity).
  rewrite le_byte_small by (cbn; lia). rewrite S0.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* bytes_at of the raw memory from the views of its bytes. *)
Lemma wcu_bytes_views : forall (W : world segs) mem a (l : list byte),
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length l) ->
     aview segs (w_H W) mem (a + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))) ->
  bytes_at I0.rsegs mem a l.
Proof.
  intros W mem a l H0 H1 HV. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite (wcu_byte_nth l i Hi).
  apply (wcu_mrd_eq W).
  specialize (HV (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in HV. exact HV.
Qed.

(* writable_at reads the one byte. *)
Lemma wcu_writable_tp : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  YP09.writable_at segs (mrestrict H m) a -> YP09.writable_at segs (mrestrict H m') a.
Proof. intros H m m' a E W. unfold YP09.writable_at, mrestrict in *. unfold wview in *. rewrite E. exact W. Qed.

(* A visible byte a call keeps present stays writable (the leaf posts give the views and the presence, not the
   raw bytes). *)
Lemma wcu_writable_pres : forall (W : world segs) (m m' : word -> option byte) a,
  YP09.writable_at segs (mrestrict (w_H W) m) a -> w_H W (Z_to_bv 64 a) = false ->
  (forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
  YP09.writable_at segs (mrestrict (w_H W) m') a.
Proof.
  intros W m m' a Hw Hh Hp.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  - destruct (Hp a (conj Hh (ex_intro _ b Em))) as (_ & b' & Hb').
    unfold YP09.writable_at, wview, mrestrict. rewrite Hh, Hb'. discriminate.
  - unfold YP09.writable_at, wview, mrestrict in *. rewrite Hh in *. rewrite Em in Hw.
    destruct (m' (Z_to_bv 64 a)) as [b'|]; [discriminate | exact Hw].
Qed.

(* The frame write of a run keeps AR: the frame [lo, hi) is in the stack (no owned byte, AR_stack_law) and present
   (no hidden byte); every byte outside it keeps its view and its raw byte. *)
Lemma wcu_mem_post : forall B ly S (W : world segs) mem md mem' md' lo hi,
  @AR rc segs B ly S W mem md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  YK1b.mem_grows mem mem' -> munch [(lo, hi)] mem mem' -> same_but_materialized md md' ->
  @AR rc segs B ly S W mem' md' /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview segs (w_H W) mem' x = aview segs (w_H W) mem x) /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x).
Proof.
  intros B ly S W mem md mem' md' lo hi HAR Hlo Hhi HP HG HM HS.
  assert (HVIS : forall x, lo <= x < hi -> w_H W (Z_to_bv 64 x) = false) by (intros x Hx; exact (proj1 (HP x Hx))).
  assert (HPR : forall x, lo <= x < hi -> mem' (Z_to_bv 64 x) <> None).
  { intros x Hx. destruct (HP x Hx) as (_ & b & Hb). apply HG. rewrite Hb. discriminate. }
  assert (OUT : forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x).
  { intros x Hx. apply HM. cbn [outside]. split; [exact Hx | exact I]. }
  split; [|split; [|split]].
  - apply (LF.AR_sbm_stmt_YG0q segs B ly S W mem' md md'); [|exact HS].
    apply (LF.AR_frame_stmt_YG0q segs B ly S W mem md mem' HAR).
    + intros a Ha Hown. apply (LF.aview_ext_stmt_YG0n segs). apply OUT. rewrite unsigned_lit by lia.
      intros Hin. exact (LF.AR_stack_stmt_YG0s segs B ly S W mem md a HAR ltac:(lia) Hown).
    + intros a Hv.
      destruct (Z_le_gt_dec lo (bv_unsigned (Z_to_bv 64 a))) as [H1|H1];
        [destruct (Z_lt_ge_dec (bv_unsigned (Z_to_bv 64 a)) hi) as [H2|H2]|].
      * apply (LF.aview_some_stmt_YG0n segs).
        -- rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 a)). apply HVIS. lia.
        -- rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 a)). apply HPR. lia.
      * rewrite (LF.aview_ext_stmt_YG0n segs (w_H W) mem mem' a); [exact Hv|]. apply OUT. lia.
      * rewrite (LF.aview_ext_stmt_YG0n segs (w_H W) mem mem' a); [exact Hv|]. apply OUT. lia.
    + intros a Ha. apply OUT. intros Hin.
      pose proof (HVIS _ Hin) as Hf. rewrite Z_to_bv_bv_unsigned in Hf. congruence.
  - intros x Hx Hn. apply (LF.aview_ext_stmt_YG0n segs). apply OUT. rewrite unsigned_lit by exact Hx. exact Hn.
  - intros x Hx Hn. apply OUT. rewrite unsigned_lit by exact Hx. exact Hn.
  - intros x (HxH & b & Hb). split; [exact HxH|].
    destruct (mem' (Z_to_bv 64 x)) as [b'|] eqn:Hb'; [exists b'; reflexivity|].
    exfalso. refine (HG (Z_to_bv 64 x) _ Hb'). rewrite Hb. discriminate.
Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr. *)
Lemma wcu_run : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (pc : Z)
    (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF I0.rsegs (LK.RNG_W (world segs) (@w_H segs) W) P (@LK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms1, P ms1 /\ Regs6ss.ms_eqv ms1 ms' /\ YK1b.mem_grows mem (ms_mem ms1)) ->
     same_but_materialized md md' -> SRr segs W (mkCfg ms' md') Q) ->
  SRr segs W (@cfg_at fx segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q HR K.
  pose proof (LG.evtF_eqv I0.rsegs _ P _ _ HR (LG.ms_of_regs_eqv pc regs mem)) as HR'.
  assert (FPA : LK.fp_avoids (w_H W) (LK.RNG_W (world segs) (@w_H segs) W)).
  { intros a n Ha. unfold LK.RNG_W in Ha. rewrite Z_to_bv_bv_unsigned in Ha. exact Ha. }
  exact (LF.bridge_evtF_stmt_YA0n W _ md _ _ Q HR' FPA K).
Qed.

(* The frame cells carried to a memory with the same views and presence over them. *)
Lemma wcu_frame_tp : forall (W : world segs) (m m' : word -> option byte) A cs,
  rw_cells I0.rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> apresent (w_H W) m (A + i)) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> apresent (w_H W) m' (A + i)) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> aview segs (w_H W) m' (A + i) = aview segs (w_H W) m (A + i)) ->
  rw_cells I0.rsegs m' A cs.
Proof.
  intros W m m' A cs FR HP HP' HV. apply (wcu_rw_cells_eq m m' A cs FR).
  intros i Hi. unfold wa. apply (wcu_byte_eq (w_H W) (w_H W) m m'); [exact (HP i Hi) | exact (HP' i Hi) | exact (HV i Hi)].
Qed.

End Glue.

(* The shadow hull of a sub-range lies in the hull of the range. *)
Lemma wcu_hull_sub : forall (rd : Z -> option Z) f n a k, 0 <= f -> f <= a -> 0 < k -> a + k <= f + n ->
  shadow_hull_vis rd f n -> shadow_hull_vis rd a k.
Proof.
  intros rd f n a k H0 H1 Hk H2 HV s Hs. apply HV. unfold shadow_addr, SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma wcu_ra_sub : forall (rd : Z -> option Z) f n a k, f <= a -> a + k <= f + n ->
  range_addressable rd SHADOW_OFF f n -> range_addressable rd SHADOW_OFF a k.
Proof. intros rd f n a k H1 H2 HR x Hx. apply HR. lia. Qed.

(* ---- the walk ---- *)

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The statement's post (lib/B/Prog/rp_copy_untag_cg.v wire_rp_copy_untag_cg), as the tail below concludes it. *)
Definition wcu_post (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (f n : Z) (bs : list byte) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
     c' = @cfg_at fx segs (raZ regs) regs' mem' md' /\
     @AR rc segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
     YK11.getr regs' 10 = w64 (PRc.copy_untag_result n bs) /\
     (50 <= n -> forall i, 0 <= i < n ->
        aview segs (w_H W) mem' (f + i) = Some (PRc.cu_byte (PRc.cu_bytes n bs) (Z.to_nat i))) /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ (PRc.cu_moves n bs = true /\ f + 12 <= x < f + n - 4) ->
        ~ (spZ regs - RCU_STK <= x < spZ regs) -> aview segs (w_H W) mem' x = aview segs (w_H W) mem x) /\
     (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x).

(* From the call of reac_frame_is_reac (0x8183c, +0x74) to the return: the leaf (its premises read from the views
   of the call state), rcu_seg_leaf_ret, the post. Both paths reach it: with the tag after the memmove (a1 = n - 4),
   without it from the tag return (a1 = n); L is cu_len n bs either way and the frame holds cu_bytes n bs. *)
Lemma wcu_tail : forall ly S (W : world segs) regs mem md (f n : Z) (bs junk : list byte)
    (Rl : bvmap 5 word) (ml : word -> option byte) (mdl : Model),
  wire_cells B ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LIR.wire_reac_frame_is_reac_cg) fx') ->
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + RCU_STK <= spZ regs ->
  (forall x, spZ regs - RCU_STK <= x < spZ regs -> apresent (w_H W) mem x) ->
  0 < f -> f + n <= 2 ^ 63 -> 50 <= n <= RCU_LEN_MAX -> Z.of_nat (length bs) = n ->
  (forall x, f <= x < f + n -> ~ (spZ regs - RCU_STK <= x < spZ regs)) ->
  amem_range f n ->
  @AR rc segs B ly S W ml mdl -> same_but_materialized md mdl ->
  YK11.getr Rl (Z_to_bv 5 1) = Z_to_bv 64 0x8148c ->
  YK11.getr Rl (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48) ->
  YK11.getr Rl (Z_to_bv 5 3) = YK11.getr regs (Z_to_bv 5 3) ->
  YK11.getr Rl (Z_to_bv 5 4) = YK11.getr regs (Z_to_bv 5 4) ->
  bv_unsigned (YK11.getr Rl (Z_to_bv 5 8)) = PRc.cu_len n bs ->
  bv_unsigned (YK11.getr Rl (Z_to_bv 5 9)) = f ->
  bv_unsigned (YK11.getr Rl (Z_to_bv 5 10)) = f ->
  bv_unsigned (YK11.getr Rl (Z_to_bv 5 11)) = PRc.cu_len n bs ->
  bv_unsigned (YK11.getr Rl (Z_to_bv 5 18)) = f + 16 ->
  YK11.getr Rl (Z_to_bv 5 19) = Z_to_bv 64 2147450880 ->
  (forall q, 20 <= q <= 27 -> YK11.getr Rl (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)) ->
  rw_cells I0.rsegs ml (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48)
    [CB 8 junk; C8 (YK11.getr regs (Z_to_bv 5 19)); C8 (YK11.getr regs (Z_to_bv 5 18));
     C8 (YK11.getr regs (Z_to_bv 5 9)); C8 (YK11.getr regs (Z_to_bv 5 8)); C8 (YK11.getr regs (Z_to_bv 5 1))] ->
  (forall i, 0 <= i < n -> aview segs (w_H W) ml (f + i) = Some (PRc.cu_byte (PRc.cu_bytes n bs) (Z.to_nat i))) ->
  range_addressable (aview segs (w_H W) ml) SHADOW_OFF f n ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (PRc.cu_moves n bs = true /\ f + 12 <= x < f + n - 4) ->
     ~ (spZ regs - RCU_STK <= x < spZ regs) -> aview segs (w_H W) ml x = aview segs (w_H W) mem x) ->
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) ml x) ->
  SRr segs W (@cfg_at fx segs 0x8183c Rl ml mdl) (wcu_post ly S W regs mem md f n bs).
Proof.
  intros ly S W regs mem md f n bs junk Rl ml mdl HCELLS HLEAF HPRE HSTK HPRES Hf0 Hfn Hn Hlen HFR HAMR
    HARl HSl Rl1 Rl2 Rl3 Rl4 Rl8 Rl9 Rl10 Rl11 Rl18 Rl19 RlS FRl HVf HRADl HVl HPl.
  pose proof HPRE as (HAR & HRET & HAL & HLO & HHI & HSTKE & HGP & HTP).
  assert (HRET' : YK0s.ret_ok (YK11.getr regs (Z_to_bv 5 1))) by exact HRET.
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (LT1 & LT2 & LT3 & LT4 & LT5 & LT6 & LT7).
  unfold RCU_STK, RCU_FRAME, RCU_LEN_MAX, ESTACK in *.
  unfold kHighMemBeg, kHighMemEnd in LT4, LT7.
  set (RNG := LK.RNG_W (world segs) (@w_H segs) W).
  set (bs' := PRc.cu_bytes n bs) in *. set (L := PRc.cu_len n bs) in *.
  assert (HLb : length bs' = length bs) by (apply wcu_cu_bytes_length; exact Hlen).
  assert (HLr : n - 4 <= L <= n) by (unfold L; rewrite wcu_cu_len by lia; destruct (PRc.cu_tagged bs); lia).
  assert (SP : spZ regs = bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) by reflexivity.
  (* [f, f + n) lies wholly below the call's stack window or wholly at or above sp *)
  assert (OFFW : f + n <= spZ regs - (48 + 4096) \/ spZ regs <= f).
  { destruct (Z_le_gt_dec (spZ regs) f) as [H|H]; [right; exact H|].
    destruct (Z_le_gt_dec (f + n) (spZ regs - (48 + 4096))) as [H'|H']; [left; exact H'|].
    exfalso. apply (HFR (Z.max f (spZ regs - (48 + 4096)))); lia. }
  assert (Rl2u : bv_unsigned (YK11.getr Rl (Z_to_bv 5 2)) = spZ regs - 48)
    by (rewrite Rl2, unsigned_lit; rewrite <- SP; lia).
  assert (SPl : spZ Rl = spZ regs - 48) by exact Rl2u.
  (* the call's pre (sp' = sp - 48, ra = 0x8148c) *)
  assert (PREL : ecall_pre segs B ly S W Rl ml mdl).
  { split; [exact HARl|].
    split; [assert (Hra : YK0s.ret_ok (YK11.getr Rl (Z_to_bv 5 1)))
              by (rewrite Rl1; apply ret_ok_even; vm_compute; reflexivity); exact Hra|].
    split; [rewrite SPl; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z.mod_add by lia;
            exact HAL|].
    split; [rewrite SPl; unfold ESTACK; lia|]. split; [rewrite SPl; lia|].
    split; [intros a Ha; rewrite SPl in Ha; unfold ESTACK in Ha; apply HPl; apply HPRES; lia|].
    split; [assert (Hg : YK11.getr Rl (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite Rl3; exact HGP); exact Hg
           |assert (Ht : YK11.getr Rl (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite Rl4; exact HTP); exact Ht]. }
  (* the frame's views, bytes and shadow at the call *)
  assert (VIS : forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (f + i)) = false).
  { intros i Hi. apply (wcu_vis W ml). rewrite (HVf i Hi). discriminate. }
  assert (RA12 : range_addressable (aview segs (w_H W) ml) SHADOW_OFF (f + 12) 2)
    by (apply (wcu_ra_sub _ f n); [lia | lia | exact HRADl]).
  pose proof (HLEAF fx) as HLF. unfold wire_leaf_at, LIR.wire_reac_frame_is_reac_cg in HLF.
  specialize (HLF ly S W Rl ml mdl bs' (spZ regs - 64) PREL). cbv zeta in HLF.
  rewrite Rl10, Rl11 in HLF.
  eapply SRr_bind.
  { apply HLF.
    - rewrite Rl2u. apply (LB.wcc_leafb_stk W ml); [lia | lia |]. intros a Ha. apply HPl, HPRES. lia.
    - rewrite Rl2u. unfold LRc.REAC_FRAME_IS_REAC_FRAME. lia.
    - intros _ _. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
      + rewrite HLb. lia.
      + apply (wcu_bytes_views W ml f bs'); [lia | rewrite HLb; lia |].
        intros i Hi. rewrite (HVf i ltac:(lia)). reflexivity.
      + unfold KA.off_stk. rewrite Rl2u. unfold LRc.REAC_FRAME_IS_REAC_FRAME. lia.
      + rewrite Rl2u. unfold LRc.REAC_FRAME_IS_REAC_FRAME, UC.app_mem, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
      + rewrite Rl2u. unfold UC.app_mem, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
      + exact (LB.wcc_leafb_asan_cells B HCELLS ly S W ml mdl HARl).
      + unfold KA.off_stk. rewrite Rl2u. unfold LRc.REAC_FRAME_IS_REAC_FRAME, UC.GOT_CELL_K. lia.
      + unfold KA.off_stk. rewrite Rl2u. unfold LRc.REAC_FRAME_IS_REAC_FRAME, UC.CELL_K. lia.
      + apply (LB.wcc_leafb_addressable W ml); [exact RA12 | lia | lia | |].
        * unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR. unfold UC.APPMEM_END. lia.
        * intros i Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR.
          unfold UC.app_mem, UC.LOWMEM_END, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
    - rewrite Rl2u. unfold LRc.REAC_FRAME_IS_REAC_FRAME.
      apply (wcu_rng_vis W); [lia | lia |]. intros i Hi.
      exact (proj1 (HPl _ (HPRES (spZ regs - 48 - 16 + i) ltac:(lia)))).
    - intros _ _. split; [exact (proj1 (LB.wcc_leafb_rng_cells W))|].
      split; [exact (proj2 (LB.wcc_leafb_rng_cells W))|].
      split.
      + apply (wcu_rng_vis W); [lia | lia |]. intros i Hi.
        replace (f + 12 + i) with (f + (12 + i)) by lia. apply VIS. lia.
      + pose proof (LB.wcc_leafb_rng_shadow W ml (f + 12) 2 RA12 ltac:(lia) ltac:(lia) ltac:(lia)) as RSH12.
        unfold UC.shadow_addr in RSH12.
        replace ((f + 12 + 2 - 1) / 8 + UC.ASAN_K - ((f + 12) / 8 + UC.ASAN_K) + 1)
           with ((f + 12 + 2 - 1) / 8 - (f + 12) / 8 + 1) in RSH12 by lia.
        exact RSH12. }
  intros W' c' _ (-> & regs5 & m5 & md5 & -> & HAR5 & HAP5 & HS5 & HRES & HV5 & HP5 & _).
  specialize (HRES _ eq_refl).
  set (r := LRc.is_reac_result f L bs') in HRES.
  assert (Hr01 : r = 0 \/ r = 1) by apply wcu_reac_01.
  assert (RAl : LK.raZ Rl = 0x8148c) by (unfold LK.raZ; rewrite Rl1; reflexivity).
  rewrite RAl.
  change (LK.cfg_at 0x8148c regs5 m5 md5) with (@cfg_at fx segs 0x8148c regs5 m5 md5).
  (* what the leaf keeps: every byte outside its stack window [sp - 48 - 4096, sp - 48) *)
  assert (TV5 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - (48 + 4096) <= x < spZ regs - 48) ->
                aview segs (w_H W) m5 x = aview segs (w_H W) ml x).
  { intros x Hx Hnx. apply HV5; [exact Hx | | intros Hc; inversion Hc].
    change (LK.spZ Rl) with (spZ Rl). rewrite SPl. unfold LK.ESTACK. lia. }
  assert (G5 : forall q, acallee_saved q -> YK11.getr regs5 (Z_to_bv 5 q) = YK11.getr Rl (Z_to_bv 5 q))
    by exact HAP5.
  assert (G5_2 : YK11.getr regs5 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48))
    by (rewrite (G5 2 ltac:(unfold acallee_saved; lia)); exact Rl2).
  assert (G5_19 : YK11.getr regs5 (Z_to_bv 5 19) = Z_to_bv 64 2147450880)
    by (rewrite (G5 19 ltac:(unfold acallee_saved; lia)); exact Rl19).
  assert (G5_8 : bv_unsigned (YK11.getr regs5 (Z_to_bv 5 8)) = L)
    by (rewrite (G5 8 ltac:(unfold acallee_saved; lia)); exact Rl8).
  assert (G5_9 : bv_unsigned (YK11.getr regs5 (Z_to_bv 5 9)) = f)
    by (rewrite (G5 9 ltac:(unfold acallee_saved; lia)); exact Rl9).
  assert (G5_18 : bv_unsigned (YK11.getr regs5 (Z_to_bv 5 18)) = f + 16)
    by (rewrite (G5 18 ltac:(unfold acallee_saved; lia)); exact Rl18).
  assert (G5_10 : bv_unsigned (YK11.getr regs5 (Z_to_bv 5 10)) = r).
  { rewrite (HRES : YK11.getr regs5 (Z_to_bv 5 10) = Z_to_bv 64 r). apply unsigned_lit. lia. }
  (* the frame cells, f's bytes 16 and 17 and the shadow after the leaf *)
  assert (FR5 : rw_cells I0.rsegs m5 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48)
    [CB 8 junk; C8 (YK11.getr regs (Z_to_bv 5 19)); C8 (YK11.getr regs (Z_to_bv 5 18));
     C8 (YK11.getr regs (Z_to_bv 5 9)); C8 (YK11.getr regs (Z_to_bv 5 8)); C8 (YK11.getr regs (Z_to_bv 5 1))]).
  { apply (wcu_frame_tp W ml m5 _ _ FRl); cbn [cells_size csize Nat.add]; intros i Hi;
      change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs).
    - apply HPl, HPRES. lia.
    - apply HP5, HPl, HPRES. lia.
    - apply TV5; lia. }
  assert (V5 : forall i, 0 <= i < n -> aview segs (w_H W) m5 (f + i) = Some (PRc.cu_byte bs' (Z.to_nat i))).
  { intros i Hi. rewrite TV5 by lia. exact (HVf i Hi). }
  assert (SH5 : forall x, f <= x < f + n ->
     exists k : byte, mrd I0.rsegs m5 (wa (x / 8 + UC.ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)).
  { intros x Hx. destruct (HRADl x Hx) as (s & Hs & Hok).
    destruct (wcu_shadow_off f n x HAMR ltac:(lia) Hx) as (Lx & _).
    assert (Hs5 : aview segs (w_H W) m5 (shadow_of_addr SHADOW_OFF x) = Some s) by (rewrite TV5; [exact Hs | lia | lia]).
    destruct (wcu_mrd W m5 _ _ Hs5) as (kb & Hkb & Hu).
    exists kb. replace (x / 8 + UC.ASAN_K) with (shadow_of_addr SHADOW_OFF x)
      by (unfold shadow_of_addr, SHADOW_OFF, UC.ASAN_K; lia).
    split; [exact Hkb|]. unfold saddr_ok in Hok. rewrite wcu_signed_small by lia. rewrite Hu. lia. }
  assert (RD5 : forall x, f <= x < f + n -> ExecF.rng RNG x 1).
  { intros x Hx. apply (wcu_rng_vis W); [lia | lia |]. intros i Hi. replace (x + i) with (f + (x - f)) by lia.
    apply VIS. lia. }
  assert (RS5 : forall x, f <= x < f + n -> ExecF.rng RNG (x / 8 + UC.ASAN_K) 1).
  { intros x Hx. destruct (HRADl x Hx) as (s & Hs & _).
    destruct (wcu_shadow_off f n x HAMR ltac:(lia) Hx) as (Lx & _). unfold shadow_of_addr, SHADOW_OFF in Lx, Hs.
    apply (wcu_rng_vis W); [unfold UC.ASAN_K; lia | unfold UC.ASAN_K; lia |]. intros i Hi.
    replace (x / 8 + UC.ASAN_K + i) with (2147450880 + x / 8) by (unfold UC.ASAN_K; lia).
    apply (wcu_vis W ml). rewrite Hs. discriminate. }
  assert (M16 : mrd I0.rsegs m5 (wa (f + 16)) = Some (nth 16 bs' (Z_to_bv 8 0))).
  { apply (wcu_mrd_eq W). rewrite (V5 16 ltac:(lia)). reflexivity. }
  assert (M17 : mrd I0.rsegs m5 (wa (f + 17)) = Some (nth 17 bs' (Z_to_bv 8 0))).
  { apply (wcu_mrd_eq W). rewrite (V5 17 ltac:(lia)). reflexivity. }
  assert (RFR : ExecF.rng RNG (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48) 48).
  { rewrite <- SP. apply (wcu_rng_vis W); [lia | lia |]. intros i Hi.
    exact (proj1 (HPRES (spZ regs + -48 + i) ltac:(lia))). }
  (* rcu_seg_leaf_ret from 0x8148c *)
  eapply wcu_run.
  { unfold LK.ms_of_regs. rewrite G5_2, G5_19. change (LK.w64 0x8148c) with (Z_to_bv 64 0x8148c).
    eapply (RR.rcu_seg_leaf_ret RNG) with (LO := f) (HI := f + n) (f := f) (r := r) (L := L)
      (b16 := nth 16 bs' (Z_to_bv 8 0)) (b17 := nth 17 bs' (Z_to_bv 8 0)) (junk := junk)
      (ra := YK11.getr regs (Z_to_bv 5 1)) (sp := YK11.getr regs (Z_to_bv 5 2))
      (c0 := YK11.getr regs (Z_to_bv 5 8)) (c1 := YK11.getr regs (Z_to_bv 5 9))
      (c2 := YK11.getr regs (Z_to_bv 5 18)) (c3 := YK11.getr regs (Z_to_bv 5 19)).
    all: first [ exact FR5 | exact RFR | exact SH5 | exact RD5 | exact RS5 | exact M16 | exact M17
               | exact G5_8 | exact G5_9 | exact G5_10 | exact G5_18 | exact Hr01 | exact Hf0
               | (rewrite <- SP; lia) | lia ]. }
  intros ms' md6 (ms1 & (y10 & y11 & y12 & Ey & ->) & HE6 & _) HS6.
  destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE6) as (R6 & -> & HX6).
  apply SRr_ret. unfold wcu_post. split; [reflexivity|]. exists R6, m5, md6.
  split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned, (LF.ret_ok_stmt_YK0s _ HRET'); reflexivity|].
  split; [exact (LF.AR_sbm_stmt_YG0q segs B ly S W m5 md5 md6 HAR5 HS6)|].
  split.
  { intros q Hq. rewrite (LG.getr_xeqv _ _ HX6). unfold acallee_saved in Hq.
    assert (Hq' : q = 2 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 3 \/ q = 4 \/ (20 <= q <= 27)) by lia.
    destruct Hq' as [->|[->|[->|[->|[->|[->|[->|Hq']]]]]]];
      [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity| | |].
    - transitivity (YK11.getr regs5 (Z_to_bv 5 3)); [reflexivity|].
      rewrite (G5 3 ltac:(unfold acallee_saved; lia)). exact Rl3.
    - transitivity (YK11.getr regs5 (Z_to_bv 5 4)); [reflexivity|].
      rewrite (G5 4 ltac:(unfold acallee_saved; lia)). exact Rl4.
    - transitivity (YK11.getr regs5 (Z_to_bv 5 q)).
      + assert (Hq'' : q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
        repeat (destruct Hq'' as [->|Hq'']; [reflexivity|]). subst q. reflexivity.
      + rewrite (G5 q ltac:(unfold acallee_saved; lia)). exact (RlS q Hq'). }
  split; [exact (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ HSl HS5) HS6)|].
  split.
  { rewrite (LG.getr_xeqv _ _ HX6). transitivity y10; [reflexivity|].
    apply bv_eq. unfold w64. rewrite Ey.
    assert (EQ : (if r =? 0 then 0
                  else if (bv_unsigned (nth 16 bs' (Z_to_bv 8 0)) =? 0) && (bv_unsigned (nth 17 bs' (Z_to_bv 8 0)) =? 0)
                       then L else 0)%bool = PRc.copy_untag_result n bs)
      by (unfold r, bs', L; apply wcu_result; lia).
    rewrite EQ. rewrite unsigned_lit; [reflexivity|].
    rewrite <- EQ. destruct (r =? 0); [lia|].
    destruct ((bv_unsigned (nth 16 bs' (Z_to_bv 8 0)) =? 0) && (bv_unsigned (nth 17 bs' (Z_to_bv 8 0)) =? 0))%bool; lia. }
  split; [intros _ i Hi; exact (V5 i Hi)|].
  split.
  { intros x Hx Hmv Hnx. unfold RCU_STK, RCU_FRAME, ESTACK in Hnx. rewrite TV5; [| exact Hx | lia].
    apply HVl; [exact Hx | exact Hmv | exact Hnx]. }
  intros x Hx. exact (HP5 x (HPl x Hx)).
Qed.

Lemma wire_rp_copy_untag_holds_at : @wire_rp_copy_untag_holds_stmt fx rc B.
Proof.
  intros HCELLS LAWS HMM HTAG HLEAF.
  unfold wire_rp_copy_untag_cg.
  intros ly S W regs mem md f n bs HPRE HSTK HPRES Hf Hn Hnr Hlen HBIG.
  change (SRr segs W (@cfg_at fx segs (wire_sigma WS_rp_copy_untag) regs mem md) (wcu_post ly S W regs mem md f n bs)).
  pose proof HPRE as (HAR & HRET & HAL & HLO & HHI & HSTKE & HGP & HTP).
  assert (HRET' : YK0s.ret_ok (YK11.getr regs (Z_to_bv 5 1))) by exact HRET.
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (LT1 & LT2 & LT3 & LT4 & LT5 & LT6 & LT7).
  pose proof HSTK as HSTK0. pose proof HPRES as HPRES0.
  unfold RCU_STK, RCU_FRAME, RCU_LEN_MAX, ESTACK in HSTK, HPRES, Hnr, HBIG.
  unfold kHighMemBeg, kHighMemEnd in LT4, LT7.
  set (RNG := LK.RNG_W (world segs) (@w_H segs) W).
  assert (SP : spZ regs = bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) by reflexivity.
  (* the caller's stack below sp, the frame and its footprint *)
  assert (STK : stk I0.rsegs mem (spZ regs - (48 + 4096)) (spZ regs)).
  { split; [lia|]. split; [lia|].
    intros a Ha. destruct (HPRES a Ha) as [_ [b Hb]]. unfold wa. split.
    - unfold wview. rewrite Hb. discriminate.
    - exists b. unfold mrd. rewrite Hb. reflexivity. }
  assert (RFR : ExecF.rng RNG (spZ regs + -48) 48).
  { apply (wcu_rng_vis W); [lia | lia |]. intros i Hi. exact (proj1 (HPRES (spZ regs + -48 + i) ltac:(lia))). }
  assert (A1 : bv_unsigned (YK11.getr regs (Z_to_bv 5 11)) = n)
    by (rewrite (Hn : YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 n); apply unsigned_lit; lia).
  destruct (Z_lt_le_dec n 50) as [Hsm|Hbig].
  - (* n < 50: rcu_seg_small to the return *)
    eapply wcu_run.
    { unfold LK.ms_of_regs. change (LK.w64 (wire_sigma WS_rp_copy_untag)) with (Z_to_bv 64 0x81414).
      eapply (RR.rcu_seg_small RNG).
      - exact STK.
      - rewrite <- SP. lia.
      - rewrite <- SP. exact RFR.
      - rewrite A1. exact Hsm. }
    intros ms' md' (ms1 & (m1 & -> & MU) & HE & HGR) HS.
    destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R2 & -> & HX).
    cbn [ms_mem] in HGR. rewrite <- SP in MU.
    destruct (wcu_mem_post B ly S W mem md m1 md' (spZ regs + -48) (spZ regs) HAR ltac:(lia) ltac:(lia)
                ltac:(intros a Ha; apply HPRES; lia) HGR MU HS) as (HAR1 & HV1 & _ & HP1).
    apply SRr_ret. unfold wcu_post. split; [reflexivity|]. exists R2, m1, md'.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned, (LF.ret_ok_stmt_YK0s _ HRET'); reflexivity|].
    split; [exact HAR1|].
    split.
    { intros q Hq. rewrite (LG.getr_xeqv _ _ HX). unfold acallee_saved in Hq.
      assert (Hq' : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
                    q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
    split; [exact HS|].
    split.
    { rewrite (LG.getr_xeqv _ _ HX). unfold PRc.copy_untag_result. rewrite (proj2 (Z.ltb_lt n 50) Hsm).
      reflexivity. }
    split; [intros Hb; lia|].
    split; [intros x Hx _ Hnx; apply HV1; [exact Hx | unfold RCU_STK, RCU_FRAME, ESTACK in Hnx; lia] | exact HP1].
  - (* n >= 50 *)
    destruct (HBIG Hbig) as (Hf0 & Hfn & HG & HFR & HAMR & HRAD & HSHV).
    assert (HFRw : forall x, f <= x < f + n -> ~ (spZ regs - (48 + 4096) <= x < spZ regs))
      by (intros x Hx; exact (proj2 (proj2 (proj2 (HFR x Hx))))).
    assert (OFFW : f + n <= spZ regs - (48 + 4096) \/ spZ regs <= f).
    { destruct (Z_le_gt_dec (spZ regs) f) as [H|H]; [right; exact H|].
      destruct (Z_le_gt_dec (f + n) (spZ regs - (48 + 4096))) as [H'|H']; [left; exact H'|].
      exfalso. apply (HFRw (Z.max f (spZ regs - (48 + 4096)))); lia. }
    (* the runtime cells: the shadow base and its GOT word *)
    destruct (HCELLS ly) as (C1 & C2 & _).
    pose proof (am_const _ _ _ _ (proj1 HAR)) as HCo. rewrite Forall_forall in HCo.
    pose proof (HCo _ C1) as K1. pose proof (HCo _ C2) as K2.
    unfold z8, c8, cell_holds in K1, K2. cbn [c_at c_val c_w aeval] in K1, K2.
    assert (BCK : bytes_at I0.rsegs mem UC.CELL_K (le8 (wa UC.ASAN_K))).
    { apply (wcu_cell8 W mem); [unfold UC.CELL_K; lia | unfold UC.CELL_K; lia | exact K1 |].
      intros k Hk. do 8 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; reflexivity]|]). lia. }
    assert (BGCK : bytes_at I0.rsegs mem UC.GOT_CELL_K (le8 (wa UC.CELL_K))).
    { apply (wcu_cell8 W mem); [unfold UC.GOT_CELL_K; lia | unfold UC.GOT_CELL_K; lia | exact K2 |].
      intros k Hk. do 8 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; reflexivity]|]). lia. }
    pose proof (LB.wcc_leafb_rng_cells W) as (RGCK & RCK).
    assert (Af : bv_unsigned (YK11.getr regs (Z_to_bv 5 10)) = f)
      by (rewrite (Hf : YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 f); apply unsigned_lit; lia).
    (* rcu_seg_call_tag to the is_tagged_reac call at 0x8103c *)
    eapply wcu_run.
    { unfold LK.ms_of_regs. change (LK.w64 (wire_sigma WS_rp_copy_untag)) with (Z_to_bv 64 0x81414).
      eapply (RR.rcu_seg_call_tag RNG) with (f := f) (n := n).
      - exact STK.
      - rewrite <- SP. lia.
      - exact BGCK.
      - exact BCK.
      - rewrite <- SP. unfold UC.CELL_K. lia.
      - rewrite <- SP. exact RFR.
      - exact RGCK.
      - exact RCK.
      - exact Af.
      - exact A1.
      - lia.
      - exact Hf0. }
    intros ms' md1 (ms1 & (m1 & junk & -> & MU & FR1) & HE & HGR) HS1.
    destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R1 & -> & HX1).
    cbn [ms_mem] in HGR. rewrite <- SP in MU.
    destruct (wcu_mem_post B ly S W mem md m1 md1 (spZ regs + -48) (spZ regs) HAR ltac:(lia) ltac:(lia)
                ltac:(intros a Ha; apply HPRES; lia) HGR MU HS1) as (HAR1 & HV1 & HRAW1 & HP1).
    assert (R1_1 : YK11.getr R1 (Z_to_bv 5 1) = Z_to_bv 64 0x81450) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_2 : YK11.getr R1 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48))
      by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_3 : YK11.getr R1 (Z_to_bv 5 3) = YK11.getr regs (Z_to_bv 5 3)) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_4 : YK11.getr R1 (Z_to_bv 5 4) = YK11.getr regs (Z_to_bv 5 4)) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_8 : YK11.getr R1 (Z_to_bv 5 8) = YK11.getr regs (Z_to_bv 5 11)) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_9 : YK11.getr R1 (Z_to_bv 5 9) = YK11.getr regs (Z_to_bv 5 10)) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_10 : YK11.getr R1 (Z_to_bv 5 10) = YK11.getr regs (Z_to_bv 5 10)) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_18 : YK11.getr R1 (Z_to_bv 5 18) = YK11.getr regs (Z_to_bv 5 18)) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_19 : YK11.getr R1 (Z_to_bv 5 19) = Z_to_bv 64 2147450880) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_S : forall q, 20 <= q <= 27 -> YK11.getr R1 (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)).
    { intros q Hq. rewrite (LG.getr_xeqv _ _ HX1).
      assert (Hq' : q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
    assert (SP1 : spZ R1 = spZ regs - 48).
    { change (spZ R1) with (bv_unsigned (YK11.getr R1 (Z_to_bv 5 2))). rewrite R1_2, unsigned_lit by lia. lia. }
    (* f's bytes, their shadow and hull at m1: the entry's (the frame write is outside them) *)
    assert (VF1 : forall i, 0 <= i < n ->
                  aview segs (w_H W) m1 (f + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).
    { intros i Hi. rewrite HV1; [| lia | lia].
      replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia. apply wcu_frame_view; [exact HG | lia]. }
    assert (TS1 : forall x, f <= x < f + n ->
                  aview segs (w_H W) m1 (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
    { intros x Hx. destruct (wcu_shadow_off f n x HAMR ltac:(lia) Hx) as (Lx & _). apply HV1; lia. }
    assert (RA1 : range_addressable (aview segs (w_H W) m1) SHADOW_OFF f n).
    { intros x Hx. destruct (HRAD x Hx) as (s & Hs & Hok). exists s. split; [rewrite TS1; [exact Hs | exact Hx] | exact Hok]. }
    assert (SHV1 : shadow_hull_vis (aview segs (w_H W) m1) f n).
    { intros s Hs. destruct (wcu_hull_off f n f n s HAMR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hs) as (Ls & _).
      rewrite HV1; [exact (HSHV s Hs) | lia | lia]. }
    assert (VIS : forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (f + i)) = false).
    { intros i Hi. apply (wcu_vis W m1). rewrite (VF1 i Hi). discriminate. }
    assert (SH1 : forall x, f <= x < f + n ->
       exists k : byte, mrd I0.rsegs m1 (wa (x / 8 + UC.ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)).
    { intros x Hx. destruct (RA1 x Hx) as (s & Hs & Hok).
      destruct (wcu_mrd W m1 _ _ Hs) as (kb & Hkb & Hu).
      exists kb. replace (x / 8 + UC.ASAN_K) with (shadow_of_addr SHADOW_OFF x)
        by (unfold shadow_of_addr, SHADOW_OFF, UC.ASAN_K; lia).
      split; [exact Hkb|]. unfold saddr_ok in Hok. rewrite wcu_signed_small by lia. rewrite Hu. lia. }
    assert (MB : forall i, 0 <= i < n -> mrd I0.rsegs m1 (wa (f + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros i Hi. apply (wcu_mrd_eq W). exact (VF1 i Hi). }
    (* the call's pre and the leaf's premises *)
    assert (PRE1 : ecall_pre segs B ly S W R1 m1 md1).
    { split; [exact HAR1|].
      split; [assert (Hra : YK0s.ret_ok (YK11.getr R1 (Z_to_bv 5 1)))
                by (rewrite R1_1; apply ret_ok_even; vm_compute; reflexivity); exact Hra|].
      split; [rewrite SP1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z.mod_add by lia;
              exact HAL|].
      split; [rewrite SP1; unfold ESTACK; lia|]. split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; unfold ESTACK in Ha; apply HP1; apply HPRES; lia|].
      split; [assert (Hg : YK11.getr R1 (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite R1_3; exact HGP); exact Hg
             |assert (Ht : YK11.getr R1 (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite R1_4; exact HTP); exact Ht]. }
    assert (TA0 : bv_unsigned (YK11.getr R1 (Z_to_bv 5 10)) = f) by (rewrite R1_10; exact Af).
    assert (RA12 : range_addressable (aview segs (w_H W) m1) SHADOW_OFF (f + 12) 2)
      by (apply (wcu_ra_sub _ f n); [lia | lia | exact RA1]).
    assert (RA16 : range_addressable (aview segs (w_H W) m1) SHADOW_OFF (f + 16) 2)
      by (apply (wcu_ra_sub _ f n); [lia | lia | exact RA1]).
    eapply SRr_bind.
    { pose proof (HTAG fx) as HTF. unfold wire_leaf_at, LIT.wire_is_tagged_reac_cg in HTF.
      specialize (HTF ly S W R1 m1 md1 bs (spZ regs - 64) PRE1). cbv zeta in HTF.
      rewrite TA0 in HTF. unfold LTc.IS_TAGGED_REAC_FRAME in HTF.
      assert (SPu : bv_unsigned (YK11.getr R1 (Z_to_bv 5 2)) = spZ regs - 48) by exact SP1.
      rewrite SPu in HTF.
      apply HTF; clear HTF.
      - lia.
      - lia.
      - apply (wcu_bytes_views W m1 f bs); [lia | lia |].
        intros i Hi. exact (VF1 i ltac:(lia)).
      - apply (LB.wcc_leafb_stk W m1); [lia | lia |]. intros a Ha. apply HP1, HPRES. lia.
      - lia.
      - unfold KA.off_stk. rewrite SPu. lia.
      - unfold UC.app_mem, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
      - unfold UC.app_mem, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
      - exact (LB.wcc_leafb_asan_cells B HCELLS ly S W m1 md1 HAR1).
      - unfold KA.off_stk. rewrite SPu. unfold UC.GOT_CELL_K. lia.
      - unfold KA.off_stk. rewrite SPu. unfold UC.CELL_K. lia.
      - apply (LB.wcc_leafb_addressable W m1); [exact RA12 | lia | lia | |].
        + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR. unfold UC.APPMEM_END. lia.
        + intros i Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR.
          unfold UC.app_mem, UC.LOWMEM_END, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
      - apply (LB.wcc_leafb_addressable W m1); [exact RA16 | lia | lia | |].
        + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR. unfold UC.APPMEM_END. lia.
        + intros i Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR.
          unfold UC.app_mem, UC.LOWMEM_END, UC.HIGHMEM_BEG, UC.APPMEM_END. lia.
      - apply (wcu_rng_vis W); [lia | lia |]. intros i Hi.
        exact (proj1 (HP1 _ (HPRES (spZ regs - 48 - 16 + i) ltac:(lia)))).
      - exact RGCK.
      - exact RCK.
      - apply (wcu_rng_vis W); [lia | lia |]. intros i Hi.
        replace (f + 12 + i) with (f + (12 + i)) by lia. apply VIS. lia.
      - apply (wcu_rng_vis W); [lia | lia |]. intros i Hi.
        replace (f + 16 + i) with (f + (16 + i)) by lia. apply VIS. lia.
      - pose proof (LB.wcc_leafb_rng_shadow W m1 (f + 12) 2 RA12 ltac:(lia) ltac:(lia) ltac:(lia)) as RS12.
        replace (f + 12 + 2 - 1) with (f + 13) in RS12 by lia. exact RS12.
      - pose proof (LB.wcc_leafb_rng_shadow W m1 (f + 16) 2 RA16 ltac:(lia) ltac:(lia) ltac:(lia)) as RS16.
        replace (f + 16 + 2 - 1) with (f + 17) in RS16 by lia. exact RS16. }
    intros W' c' _ (-> & regs2 & m2 & md2 & -> & HAR2 & HAP2 & HS2 & HRESt & HV2 & HP2 & _).
    specialize (HRESt _ eq_refl).
    assert (RAt : LK.raZ R1 = 0x81450) by (unfold LK.raZ; rewrite R1_1; reflexivity).
    rewrite RAt.
    change (LK.cfg_at 0x81450 regs2 m2 md2) with (@cfg_at fx segs 0x81450 regs2 m2 md2).
    assert (TV2 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - (48 + 4096) <= x < spZ regs - 48) ->
                  aview segs (w_H W) m2 x = aview segs (w_H W) m1 x).
    { intros x Hx Hnx. apply HV2; [exact Hx | | intros Hc; inversion Hc].
      change (LK.spZ R1) with (spZ R1). rewrite SP1. unfold LK.ESTACK. lia. }
    assert (G2 : forall q, acallee_saved q -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr R1 (Z_to_bv 5 q))
      by exact HAP2.
    assert (G2_10 : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 10)) = LTc.is_tagged_result bs).
    { rewrite (HRESt : YK11.getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 (LTc.is_tagged_result bs)).
      apply unsigned_lit. unfold LTc.is_tagged_result. destruct (PRc.cu_tagged bs); lia. }
    assert (G2_8 : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 8)) = n)
      by (rewrite (G2 8 ltac:(unfold acallee_saved; lia)), R1_8; exact A1).
    assert (G2_9 : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 9)) = f)
      by (rewrite (G2 9 ltac:(unfold acallee_saved; lia)), R1_9; exact Af).
    (* f's bytes and shadow at m2: the leaf wrote only its own stack window *)
    assert (VF2 : forall i, 0 <= i < n ->
                  aview segs (w_H W) m2 (f + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).
    { intros i Hi. rewrite TV2 by lia. exact (VF1 i Hi). }
    assert (TS2 : forall x, f <= x < f + n ->
                  aview segs (w_H W) m2 (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) m1 (shadow_of_addr SHADOW_OFF x)).
    { intros x Hx. destruct (wcu_shadow_off f n x HAMR ltac:(lia) Hx) as (Lx & _). apply TV2; lia. }
    assert (RA2 : range_addressable (aview segs (w_H W) m2) SHADOW_OFF f n).
    { intros x Hx. destruct (RA1 x Hx) as (s & Hs & Hok). exists s. split; [rewrite TS2; [exact Hs | exact Hx] | exact Hok]. }
    assert (SHV2 : shadow_hull_vis (aview segs (w_H W) m2) f n).
    { intros s Hs. destruct (wcu_hull_off f n f n s HAMR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hs) as (Ls & Os).
      rewrite TV2; [exact (SHV1 s Hs) | lia | lia]. }
    assert (FR2 : rw_cells I0.rsegs m2 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48)
      [CB 8 junk; C8 (YK11.getr regs (Z_to_bv 5 19)); C8 (YK11.getr regs (Z_to_bv 5 18));
       C8 (YK11.getr regs (Z_to_bv 5 9)); C8 (YK11.getr regs (Z_to_bv 5 8)); C8 (YK11.getr regs (Z_to_bv 5 1))]).
    { apply (wcu_frame_tp W m1 m2 _ _ FR1); cbn [cells_size csize Nat.add]; intros i Hi;
        change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs).
      - apply HP1, HPRES. lia.
      - apply HP2, HP1, HPRES. lia.
      - apply TV2; lia. }
    assert (CLT : PRc.cu_len n bs = if PRc.cu_tagged bs then n - 4 else n) by (apply wcu_cu_len; lia).
    (* rcu_seg_tag_ret from 0x81450 *)
    eapply wcu_run.
    { unfold LK.ms_of_regs. change (LK.w64 0x81450) with (Z_to_bv 64 0x81450).
      eapply (RR.rcu_seg_tag_ret RNG) with (f := f) (n := n) (r := LTc.is_tagged_result bs).
      - exact G2_9.
      - exact G2_8.
      - exact G2_10.
      - exact (wcu_tag_01 bs).
      - lia.
      - exact Hf0.
      - lia. }
    intros ms2 md3 (ms2' & (y18 & E18 & HALT) & HE3 & _) HS3.
    destruct HALT as [(T & y10 & y11 & y12 & E10 & E11 & E12 & ->) | (T & y10 & y11 & E10 & E11 & ->)].
    + (* the tag: memmove (f + 12, f + 16, n - 16), then rcu_seg_mm_ret, then the tail *)
      destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE3) as (R3 & -> & HX3).
      pose proof (LF.AR_sbm_stmt_YG0q segs B ly S W m2 md2 md3 HAR2 HS3) as HAR3.
      assert (TG : PRc.cu_tagged bs = true).
      { unfold LTc.is_tagged_result in T. destruct (PRc.cu_tagged bs); [reflexivity | lia]. }
      assert (MV : PRc.cu_moves n bs = true)
        by (unfold PRc.cu_moves; rewrite TG, (proj2 (Z.leb_le 50 n) ltac:(lia)); reflexivity).
      assert (R3_2 : YK11.getr R3 (Z_to_bv 5 2) = YK11.getr regs2 (Z_to_bv 5 2))
        by (rewrite (LG.getr_xeqv _ _ HX3); reflexivity).
      assert (G2_2 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48))
        by (rewrite (G2 2 ltac:(unfold acallee_saved; lia)); exact R1_2).
      assert (SP3 : spZ R3 = spZ regs - 48).
      { change (spZ R3) with (bv_unsigned (YK11.getr R3 (Z_to_bv 5 2))). rewrite R3_2, G2_2, unsigned_lit by lia. lia. }
      assert (G10 : YK11.getr R3 (Z_to_bv 5 10) = w64 (f + 12)).
      { rewrite (LG.getr_xeqv _ _ HX3). apply bv_eq. unfold w64. rewrite unsigned_lit by lia. exact E10. }
      assert (G11 : YK11.getr R3 (Z_to_bv 5 11) = w64 (f + 16)).
      { rewrite (LG.getr_xeqv _ _ HX3). apply bv_eq. unfold w64. rewrite unsigned_lit by lia. exact E11. }
      assert (G12 : YK11.getr R3 (Z_to_bv 5 12) = w64 (n - 16)).
      { rewrite (LG.getr_xeqv _ _ HX3). apply bv_eq. unfold w64. rewrite unsigned_lit by lia. exact E12. }
      assert (RA3 : raZ R3 = 0x8147c).
      { change (raZ R3) with (bv_unsigned (YK11.getr R3 (Z_to_bv 5 1))). rewrite (LG.getr_xeqv _ _ HX3). reflexivity. }
      assert (PRE3 : ecall_pre segs B ly S W R3 m2 md3).
      { split; [exact HAR3|].
        split; [assert (Hra : YK0s.ret_ok (YK11.getr R3 (Z_to_bv 5 1)))
                  by (rewrite (LG.getr_xeqv _ _ HX3); apply ret_ok_even; vm_compute; reflexivity); exact Hra|].
        split; [rewrite SP3; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z.mod_add by lia;
                exact HAL|].
        split; [rewrite SP3; unfold ESTACK; lia|]. split; [rewrite SP3; lia|].
        split; [intros a Ha; rewrite SP3 in Ha; unfold ESTACK in Ha; apply HP2, HP1, HPRES; lia|].
        split; [assert (Hg : YK11.getr R3 (Z_to_bv 5 3) = w64 (as_gp B))
                  by (rewrite (LG.getr_xeqv _ _ HX3); transitivity (YK11.getr regs2 (Z_to_bv 5 3)); [reflexivity|];
                      rewrite (G2 3 ltac:(unfold acallee_saved; lia)), R1_3; exact HGP); exact Hg
               |assert (Ht : YK11.getr R3 (Z_to_bv 5 4) = w64 (as_tp B))
                  by (rewrite (LG.getr_xeqv _ _ HX3); transitivity (YK11.getr regs2 (Z_to_bv 5 4)); [reflexivity|];
                      rewrite (G2 4 ltac:(unfold acallee_saved; lia)), R1_4; exact HTP); exact Ht]. }
      eapply SRr_bind.
      { exact (HMM fx ly S W R3 m2 md3 (f + 12) (f + 16) (n - 16) PRE3 G10 G11 G12 ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(intros a Ha; rewrite SP3; unfold ESTACK;
                destruct (HFR a ltac:(lia)) as (_ & Hw & Ho & Hnw);
                split; [apply (wcu_writable_pres W m1 m2 a);
                          [apply (wcu_writable_tp (w_H W) mem m1 a); [apply HRAW1; lia | exact Hw]
                          | replace a with (f + (a - f)) by lia; apply VIS; lia
                          | exact HP2] |
                        split; [exact Ho | lia]])
          ltac:(unfold amem_range in *; lia)
          ltac:(apply (wcu_ra_sub _ f n); [lia | lia | exact RA2])
          ltac:(intros Hp; apply (wcu_hull_sub _ f n); [lia | lia | lia | lia | exact SHV2])
          ltac:(lia) ltac:(lia)
          ltac:(intros a Ha; rewrite SP3; unfold ESTACK;
                split; [replace a with (f + (a - f)) by lia; rewrite (VF2 (a - f)) by lia; discriminate
                       | pose proof (HFRw a ltac:(lia)); lia])
          ltac:(unfold amem_range in *; lia)
          ltac:(apply (wcu_ra_sub _ f n); [lia | lia | exact RA2])
          ltac:(intros Hp; apply (wcu_hull_sub _ f n); [lia | lia | lia | lia | exact SHV2])). }
      intros W'' c'' _ (-> & regs4 & m4 & md4 & -> & HAR4 & HAP4 & HS4 & _ & HMV & HV4 & HP4).
      rewrite RA3.
      assert (G4 : forall q, acallee_saved q -> YK11.getr regs4 (Z_to_bv 5 q) = YK11.getr R3 (Z_to_bv 5 q))
        by exact HAP4.
      assert (R3g : forall q, q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 19 \/ 20 <= q <= 27 ->
                    YK11.getr R3 (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q)).
      { intros q Hq. rewrite (LG.getr_xeqv _ _ HX3).
        assert (Hq' : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
                      q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
        repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
      assert (R3_18 : bv_unsigned (YK11.getr R3 (Z_to_bv 5 18)) = f + 16)
        by (rewrite (LG.getr_xeqv _ _ HX3); exact E18).
      assert (G4_8 : bv_unsigned (YK11.getr regs4 (Z_to_bv 5 8)) = n).
      { rewrite (G4 8 ltac:(unfold acallee_saved; lia)), (R3g 8 ltac:(lia)). exact G2_8. }
      assert (G4_9 : bv_unsigned (YK11.getr regs4 (Z_to_bv 5 9)) = f).
      { rewrite (G4 9 ltac:(unfold acallee_saved; lia)), (R3g 9 ltac:(lia)). exact G2_9. }
      (* rcu_seg_mm_ret from 0x8147c *)
      eapply wcu_run.
      { unfold LK.ms_of_regs. change (LK.w64 0x8147c) with (Z_to_bv 64 0x8147c).
        eapply (RR.rcu_seg_mm_ret RNG) with (f := f) (n := n); [exact G4_8 | exact G4_9 | lia | exact Hf0]. }
      intros ms4 md5 (ms4' & (y8 & y10' & y11' & E8' & E10' & E11' & ->) & HE4 & _) HS5.
      destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE4) as (R4 & -> & HX4).
      (* what the memmove kept and wrote *)
      assert (TV4 : forall x, 0 <= x < 2 ^ 64 -> ~ (f + 12 <= x < f + n - 4) ->
                    ~ (spZ regs - (48 + 4096) <= x < spZ regs - 48) ->
                    aview segs (w_H W) m4 x = aview segs (w_H W) m2 x).
      { intros x Hx H1 H2. apply HV4; [exact Hx | lia | rewrite SP3; unfold ESTACK; lia]. }
      assert (TS4 : forall x, f <= x < f + n ->
                    aview segs (w_H W) m4 (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) m2 (shadow_of_addr SHADOW_OFF x)).
      { intros x Hx. destruct (wcu_shadow_off f n x HAMR ltac:(lia) Hx) as (Lx & Ox). apply TV4; lia. }
      eapply (wcu_tail ly S W regs mem md f n bs junk R4 m4 md5 HCELLS HLEAF HPRE HSTK0 HPRES0 Hf0 Hfn
                ltac:(unfold RCU_LEN_MAX; lia) Hlen HFRw HAMR).
      * exact (LF.AR_sbm_stmt_YG0q segs B ly S W m4 md4 md5 HAR4 HS5).
      * exact (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _
                 (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ HS1 HS2) HS3) HS4) HS5).
      * rewrite (LG.getr_xeqv _ _ HX4). reflexivity.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (YK11.getr regs4 (Z_to_bv 5 2)); [reflexivity|].
        rewrite (G4 2 ltac:(unfold acallee_saved; lia)), (R3g 2 ltac:(lia)). exact G2_2.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (YK11.getr regs4 (Z_to_bv 5 3)); [reflexivity|].
        rewrite (G4 3 ltac:(unfold acallee_saved; lia)), (R3g 3 ltac:(lia)),
                (G2 3 ltac:(unfold acallee_saved; lia)). exact R1_3.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (YK11.getr regs4 (Z_to_bv 5 4)); [reflexivity|].
        rewrite (G4 4 ltac:(unfold acallee_saved; lia)), (R3g 4 ltac:(lia)),
                (G2 4 ltac:(unfold acallee_saved; lia)). exact R1_4.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (bv_unsigned y8); [reflexivity|].
        rewrite E8', CLT, TG. reflexivity.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (bv_unsigned (YK11.getr regs4 (Z_to_bv 5 9))); [reflexivity|].
        exact G4_9.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (bv_unsigned y10'); [reflexivity|]. exact E10'.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (bv_unsigned y11'); [reflexivity|].
        rewrite E11', CLT, TG. reflexivity.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (bv_unsigned (YK11.getr regs4 (Z_to_bv 5 18))); [reflexivity|].
        rewrite (G4 18 ltac:(unfold acallee_saved; lia)). exact R3_18.
      * rewrite (LG.getr_xeqv _ _ HX4). transitivity (YK11.getr regs4 (Z_to_bv 5 19)); [reflexivity|].
        rewrite (G4 19 ltac:(unfold acallee_saved; lia)), (R3g 19 ltac:(lia)),
                (G2 19 ltac:(unfold acallee_saved; lia)). exact R1_19.
      * intros q Hq. rewrite (LG.getr_xeqv _ _ HX4).
        transitivity (YK11.getr regs4 (Z_to_bv 5 q)).
        { assert (Hq' : q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
          repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
        rewrite (G4 q ltac:(unfold acallee_saved; lia)), (R3g q ltac:(lia)),
                (G2 q ltac:(unfold acallee_saved; lia)). exact (R1_S q Hq).
      * apply (wcu_frame_tp W m2 m4 _ _ FR2); cbn [cells_size csize Nat.add]; intros i Hi;
          change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs).
        -- apply HP2, HP1, HPRES. lia.
        -- apply HP4, HP2, HP1, HPRES. lia.
        -- apply TV4; [lia | lia | lia].
      * intros i Hi. rewrite (wcu_cu_bytes_tag n bs i TG ltac:(lia) Hlen Hi). unfold PRc.cu_byte.
        destruct (Z.leb_spec 12 i) as [H1|H1]; destruct (Z.ltb_spec i (n - 4)) as [H2|H2]; cbn [andb].
        -- replace (f + i) with (f + 12 + (i - 12)) by lia. rewrite (HMV (i - 12) ltac:(lia)).
           replace (f + 16 + (i - 12)) with (f + (i + 4)) by lia. exact (VF2 (i + 4) ltac:(lia)).
        -- rewrite TV4 by lia. exact (VF2 i Hi).
        -- rewrite TV4 by lia. exact (VF2 i Hi).
        -- rewrite TV4 by lia. exact (VF2 i Hi).
      * intros x Hx. destruct (RA2 x Hx) as (s & Hs & Hok). exists s. split; [rewrite TS4; [exact Hs | exact Hx] | exact Hok].
      * intros x Hx Hmv Hnx. rewrite MV in Hmv.
        rewrite TV4; [| exact Hx | intros Hc; apply Hmv; split; [reflexivity | exact Hc]
                    | unfold RCU_STK, RCU_FRAME, ESTACK in Hnx; lia].
        rewrite TV2; [| exact Hx | unfold RCU_STK, RCU_FRAME, ESTACK in Hnx; lia].
        apply HV1; [exact Hx | unfold RCU_STK, RCU_FRAME, ESTACK in Hnx; lia].
      * intros x Hx. exact (HP4 x (HP2 x (HP1 x Hx))).
    + (* no tag: reac_frame_is_reac (f, n) at once, then the tail *)
      destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE3) as (R3 & -> & HX3).
      pose proof (LF.AR_sbm_stmt_YG0q segs B ly S W m2 md2 md3 HAR2 HS3) as HAR3.
      assert (NT : PRc.cu_tagged bs = false).
      { unfold LTc.is_tagged_result in T. destruct (PRc.cu_tagged bs); [lia | reflexivity]. }
      assert (NMV : PRc.cu_moves n bs = false) by (unfold PRc.cu_moves; rewrite NT, andb_false_r; reflexivity).
      assert (CB : PRc.cu_bytes n bs = bs) by (apply wcu_cu_bytes_notag; exact NT).
      assert (G2_2 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48))
        by (rewrite (G2 2 ltac:(unfold acallee_saved; lia)); exact R1_2).
      eapply (wcu_tail ly S W regs mem md f n bs junk R3 m2 md3 HCELLS HLEAF HPRE HSTK0 HPRES0 Hf0 Hfn
                ltac:(unfold RCU_LEN_MAX; lia) Hlen HFRw HAMR).
      * exact HAR3.
      * exact (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ HS1 HS2) HS3).
      * rewrite (LG.getr_xeqv _ _ HX3). reflexivity.
      * rewrite (LG.getr_xeqv _ _ HX3). transitivity (YK11.getr regs2 (Z_to_bv 5 2)); [reflexivity|]. exact G2_2.
      * rewrite (LG.getr_xeqv _ _ HX3). transitivity (YK11.getr regs2 (Z_to_bv 5 3)); [reflexivity|].
        rewrite (G2 3 ltac:(unfold acallee_saved; lia)). exact R1_3.
      * rewrite (LG.getr_xeqv _ _ HX3). transitivity (YK11.getr regs2 (Z_to_bv 5 4)); [reflexivity|].
        rewrite (G2 4 ltac:(unfold acallee_saved; lia)). exact R1_4.
      * rewrite (LG.getr_xeqv _ _ HX3). transitivity (bv_unsigned (YK11.getr regs2 (Z_to_bv 5 8))); [reflexivity|].
        rewrite CLT, NT. exact G2_8.
      * rewrite (LG.getr_xeqv _ _ HX3). transitivity (bv_unsigned (YK11.getr regs2 (Z_to_bv 5 9))); [reflexivity|].
        exact G2_9.
      * rewrite (LG.getr_xeqv _ _ HX3). exact E10.
      * rewrite (LG.getr_xeqv _ _ HX3). rewrite CLT, NT. exact E11.
      * rewrite (LG.getr_xeqv _ _ HX3). exact E18.
      * rewrite (LG.getr_xeqv _ _ HX3). transitivity (YK11.getr regs2 (Z_to_bv 5 19)); [reflexivity|].
        rewrite (G2 19 ltac:(unfold acallee_saved; lia)). exact R1_19.
      * intros q Hq. rewrite (LG.getr_xeqv _ _ HX3).
        transitivity (YK11.getr regs2 (Z_to_bv 5 q)).
        { assert (Hq' : q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
          repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
        rewrite (G2 q ltac:(unfold acallee_saved; lia)). exact (R1_S q Hq).
      * exact FR2.
      * intros i Hi. rewrite CB. exact (VF2 i Hi).
      * exact RA2.
      * intros x Hx _ Hnx. rewrite TV2; [| exact Hx | unfold RCU_STK, RCU_FRAME, ESTACK in Hnx; lia].
        apply HV1; [exact Hx | unfold RCU_STK, RCU_FRAME, ESTACK in Hnx; lia].
      * intros x Hx. exact (HP2 x (HP1 x Hx)).
Qed.

End Main.

(* The frozen statement, at every float state, run ceiling and record. *)
Theorem wire_rp_copy_untag_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms),
  @wire_rp_copy_untag_holds_stmt fx rc B.
Proof. intros fx rc B. exact (@wire_rp_copy_untag_holds_at fx rc B). Qed.
