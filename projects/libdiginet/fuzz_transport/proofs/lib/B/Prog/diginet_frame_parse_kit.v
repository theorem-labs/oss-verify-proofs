(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 276 of its 353 lines of code are new or changed and 444 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_uci's check_value in image A, proving the frozen statement
   lib/A/Prog/check_value_cg.v uci_check_value_cg_holds_stmt, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/
   crtA_walk.v, crtA_w_head.v, crtA_w_tail.v, crtA_encw.v, crtA_w_mid.v and crtA_close.v (origin/ossv/recipes
   88154566652a): footprint runs carried into SRr, an inner journal over the call's stack window, each call cut by its
   callee contract, and the helpers of those files (crtA_run, crtA_ms_shape, crtA_ms_reg, crtT_regs_of, crtA_trace0,
   crtT_chain_nil, crtA_byte_eq, crtT_rw_cells_ext, crtA_rng_vis, crtT_aj_md, crtT_not_old, crtT_perm_rm,
   crtA_addressable, crtA_rng_hull, crtA_vis_hull) restated at this unit's image. *)
(* Modified by Theorem Labs, 2026-10: the image-free helpers, the runtime-cell, aview / garr8, footprint-range and shadow lemmas of that walk (cv_u64 .. cv_stk_present, without its allocator-trace, int and permutation lemmas) taken for libdiginet/fuzz_frame's walk of diginet_frame_parse in image A: module paths changed, cv_ renamed fp_, the image's frame_seg_covers and frame_cells in place of uci_seg_covers and uci_cells. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of lib/A/Prog/diginet_frame_parse_kit.v for fuzz_frame.asan-ubsan: module paths changed (the image-B core's lib/B/YB1v.v, YE2k.v, YCbq.v / YC5d.v; lib/B/Img0.v and AsanCells.v; lib/B/Prog/DgnFrameCg.v, LeafCgKit.v, LeafCgFacts.v, LeafCgGlue.v), the image module named BImg; no statement changed. *)
(* diginet_frame_parse_kit: the helpers lib/B/Prog/diginet_frame_parse_walk.v uses at fuzz_frame.asan-ubsan's image:
   footprint runs carried into SRr (fp_run), the registers of the state a run reaches (fp_regs_of), aview read as
   mrd and garr8, the two runtime cells the walk reads (fp_cells2), and the shadow facts of a range (fp_addressable,
   fp_rng_hull). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module BImg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Img0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Lemma fp_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma fp_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma fp_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells BImg.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells BImg.rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] He.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
    assert (Hi' : A <= A + Z.of_nat i < A + Z.of_nat (cells_size cs)) by (rewrite <- L; lia).
    unfold mrd. rewrite (He _ Hi'). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi.
    unfold wview. rewrite (He (A + i)) by lia. exact (Hw i Hi).
Qed.

(* A range of visible bytes is in the walk's footprint (crtA_w_head.v crtA_rng_vis). *)
Lemma fp_rng_vis : forall (W : world tfibsegs) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a n.
Proof.
  intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids. intros kk Hk. unfold LCK.woff.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply fp_u64; lia).
  rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

Lemma fp_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (crtA_walk.v crtA_run, with the bridge of
   lib/B/Prog/LeafCgFacts.v): the walk continues from every state the transported run can reach. *)
Lemma fp_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF BImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv BImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (fp_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

(* A state register-equivalent to an MS form with the cgif float state is that cgif state (crtA_ms_shape). *)
Lemma fp_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma fp_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

(* The registers of a state register-equivalent to an `mkR` state (crtA_w_tail.v crtT_regs_of). *)
Lemma fp_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (fp_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

(* RNG_W W holds on a range of bytes the world does not hide (crtA_encw.v crtA_rng). *)
Lemma fp_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (fp_u64 b) by lia. apply H. lia.
Qed.

(* ---- aview at this image (crtA_encw.v crtA_aview_vis, crtA_aview_mrd, crtA_aview_some) ---- *)

Lemma fp_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma fp_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd BImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma fp_mrd_of_aview : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> mrd BImg.rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E. pose proof (fp_aview_vis W mem a v E) as Hv.
  rewrite (fp_aview_mrd W mem a Hv) in E.
  destruct (mrd BImg.rsegs mem (wa a)) as [b|]; cbn in E; [|discriminate].
  injection E as E. subst v. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma fp_present_vis : forall (W : world tfibsegs) m a, apresent (w_H W) m a -> aview tfibsegs (w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (fp_aview_mrd W m a Hh). unfold mrd, wa. rewrite Hb. discriminate.
Qed.

(* ---- garr8 against aview ---- *)

Lemma fp_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma fp_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (fp_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma fp_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (fp_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma fp_find_none : forall (l : list Segment) addr n s,
  find_segment l addr n = None -> In s l ->
  Z.of_N (seg_base s) <= addr -> addr + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s) -> False.
Proof.
  induction l as [|s0 l IH]; intros addr n s Hf Hin H1 H2; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s0)) addr && Z.leb (addr + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%Z
    eqn:E; [discriminate|].
  destruct Hin as [<- | Hin].
  - apply andb_false_iff in E as [E | E]; apply Z.leb_gt in E; lia.
  - exact (IH addr n s Hf Hin H1 H2).
Qed.

Lemma fp_covers_visible : forall (hd : word -> bool) a n i,
  H_off_segments tfibsegs hd -> decode_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
  hd (Z_to_bv 64 (a + i)) = false.
Proof.
  intros hd a n i Hoff Hc Hi Ht.
  unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & Hs & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  destruct (hd (Z_to_bv 64 (a + i))) eqn:E; [exfalso | reflexivity].
  pose proof (Hoff _ E) as E2.
  rewrite (fp_u64 (a + i)) in E2 by lia.
  exact (fp_find_none tfibsegs (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma fp_covers_lo : forall a n, decode_seg_covers a n = true -> 0 <= a.
Proof.
  intros a n Hc. unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & _ & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 _]. apply Z.leb_le in H1.
  pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Lemma fp_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma fp_byte_mod : forall z n k, 0 <= k -> k + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) k mod 256 = Z.shiftr z k mod 256.
Proof.
  intros z n k Hk Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma fp_mod_pow2_mod : forall v n m, 0 <= n <= m -> (v mod 2 ^ m) mod 2 ^ n = v mod 2 ^ n.
Proof.
  intros v n m Hnm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i n) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma fp_le_byte : forall (w k : nat) z v, (k < w)%nat ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (Z_to_le_bytes w z) k) = Some (le_byte v w k).
Proof.
  intros w k z v Hk Hm. rewrite fp_nth_le_bytes by exact Hk. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold le_byte. rewrite <- Hm. symmetry. apply fp_byte_mod; lia.
Qed.

Lemma fp_wa_mod : forall v (w : nat), (w <= 8)%nat ->
  bv_unsigned (wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply fp_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

Lemma fp_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (le8 (wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold le8, word_to_le_bytes.
  apply fp_le_byte; [exact Hk | apply fp_wa_mod; lia].
Qed.

Lemma fp_opt_byte_eq : forall (x y : option byte) z,
  option_map (fun b : byte => bv_unsigned b) x = Some z ->
  option_map (fun b : byte => bv_unsigned b) y = Some z -> x = y.
Proof.
  intros [x|] [y|] z Hx Hy; cbn in Hx, Hy; try discriminate.
  injection Hx as Hx. injection Hy as Hy. f_equal. apply bv_eq. congruence.
Qed.

Section Cells.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* One constant cell of B at a numeral address in a loaded segment is bytes_at under mrd (crtA_cells.v
   crt_cell_bytes, crt_z8). *)
Lemma fp_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments tfibsegs hd ->
  cell_holds B ly (aview tfibsegs hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  decode_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  bytes_at BImg.rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold bytes_at.
  split; [exact (fp_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (fp_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : mrd BImg.rsegs mem (wa (a + Z.of_nat i)) =
                YP09.mbyte tfibsegs (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold mrd, wa, YP09.mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (fp_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma fp_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments tfibsegs hd ->
  Forall (cell_holds B ly (aview tfibsegs hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> decode_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  bytes_at BImg.rsegs mem a (le8 (wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (fp_cell_bytes ly hd mem a v 8 (le8 (wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (length_le8 _) (fp_le8_byte v)).
Qed.

(* The two runtime cells diginet_frame_parse reads (the GOT word of the shadow base, and the shadow base). *)
Lemma fp_cells2 : transport_cells B ->
  forall ly S (W : world tfibsegs) mem md, @AR rc tfibsegs B ly S W mem md ->
  bytes_at BImg.rsegs mem AC.GOT_CELL_K (le8 (wa AC.CELL_K)) /\ bytes_at BImg.rsegs mem AC.CELL_K (le8 (wa AC.ASAN_K)).
Proof.
  intros HC ly S W mem md HAR.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) by (eapply am_const; exact HM).
  destruct (HC ly) as (C1 & C2 & _).
  split.
  - apply (fp_z8 ly _ mem AC.GOT_CELL_K AC.CELL_K (w_Hoff W) HK C2); vm_compute; first [reflexivity | discriminate].
  - apply (fp_z8 ly _ mem AC.CELL_K AC.ASAN_K (w_Hoff W) HK C1); vm_compute; first [reflexivity | discriminate].
Qed.
End Cells.

(* ---- shadow and addressability of a block range (crtA_encw.v crtA_addressable, crtA_rng_hull) ---- *)

Lemma fp_byte_signed : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fp_addressable {rc : YM05.RunCeil} : forall (W : world tfibsegs) mem p n,
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> 0 <= n ->
  4096 <= p /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p /\ p + n <= ASAN_CEIL) ->
  AC.addressable mem p n.
Proof.
  intros W mem p n HA Hn Happ. pose proof ASAN_CEIL_range as [CR _].
  split; [lia|]. split; [exact Hn|].
  split; [unfold AC.APPMEM_END, kLowShadowBeg, kHighMemBeg in *; lia|].
  intros i Hi. split.
  - unfold AC.app_mem, AC.LOWMEM_END, AC.HIGHMEM_BEG, AC.APPMEM_END, kLowShadowBeg, kHighMemBeg in *. lia.
  - destruct (HA (p + i) ltac:(lia)) as (s & Hs & Hok).
    pose proof (fp_mrd_of_aview W mem _ s Hs) as Hb.
    exists (Z_to_bv 8 s). split.
    + replace (AC.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
        by (unfold AC.shadow_addr, shadow_of_addr, AC.ASAN_K, SHADOW_OFF; lia).
      exact Hb.
    + unfold saddr_ok in Hok. unfold AC.shadow_ok.
      assert (Us : bv_unsigned (Z_to_bv 8 s) = s).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
      rewrite fp_byte_signed by lia. rewrite Us. lia.
Qed.

Lemma fp_shadow_addr_eq : forall a, AC.shadow_addr a = YG0f.shadow_addr a.
Proof. intros a. unfold AC.shadow_addr, YG0f.shadow_addr, AC.ASAN_K, SHADOW_OFF. lia. Qed.

Lemma fp_rng_hull : forall (W : world tfibsegs) mem x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 48 ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (AC.shadow_addr x / 8 * 8)
    (AC.shadow_addr (x + n - 1) / 8 * 8 + 8 - AC.shadow_addr x / 8 * 8).
Proof.
  intros W mem x n H0 Hn H1 H. rewrite !fp_shadow_addr_eq.
  assert (B1 : 0 <= YG0f.shadow_addr x / 8 * 8) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  assert (B2 : YG0f.shadow_addr x / 8 * 8 <= YG0f.shadow_addr (x + n - 1) / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (B3 : YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 64) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  apply fp_rng; [exact B1 | lia |]. intros s Hs.
  specialize (H s ltac:(lia)).
  destruct (aview tfibsegs (w_H W) mem s) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (fp_aview_vis W mem s v E).
Qed.

(* Present bytes form a stack range (crtA_w_head.v crtA_stk_present). *)
Lemma fp_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk BImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.
