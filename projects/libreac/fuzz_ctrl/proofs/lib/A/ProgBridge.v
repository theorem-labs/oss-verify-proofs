(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_ctrl image A: glue from ctrl's footprint runs (Lib/ExecF.v mstepsF / evtF over A/Img0 rsegs) to the kit's
   fsteps (Reusable/YK04R.v), and the footprint a call site chooses: RNG_W H, every range of visible bytes.
   With it, a callee contract `<f>_contract_F` (forall RNG, ExecF.rng RNG lo len premises -> evtF rsegs RNG P ms)
   becomes a world walk step by Reusable/YA0nR.v SRr_fevt: pick RNG := RNG_W (w_H W); fp_avoids holds by
   fp_avoids_RNG_W, and each rng premise is a visibility fact (rng_RNG_W). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0i YK11 YK04 YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AsanRT.
Import ListNotations.
Open Scope Z_scope.

Lemma fsteps_of_mstepsF : forall RNG ms ms', ExecF.mstepsF rsegs RNG ms ms' -> fsteps rsegs RNG ms ms'.
Proof.
  intros RNG ms ms' H. induction H as [ms | ms ms1 ms2 [Hs (accs & E & F)] _ IH].
  - apply fsteps_refl.
  - eapply fsteps_cons; [| exact IH]. split; [exact Hs |]. exists accs. split; [exact E | exact F].
Qed.

Lemma fevt_of_evtF : forall RNG (P : machine_state -> Prop) ms,
  ExecF.evtF rsegs RNG P ms -> exists ms', fsteps rsegs RNG ms ms' /\ P ms'.
Proof. intros RNG P ms (ms' & Hrun & HP). exists ms'. split; [exact (fsteps_of_mstepsF RNG ms ms' Hrun) | exact HP]. Qed.

(* The largest footprint a world with hidden set H admits: every range of visible bytes. *)
Definition RNG_W (H : word -> bool) : ExecF.footprint := fun b n => range_avoids H (Z_to_bv 64 b) n.

Lemma fp_avoids_RNG_W : forall H, fp_avoids H (RNG_W H).
(* `Z_to_bv_bv_unsigned` named by its full path: Locate in this file's context (10-29 06:59Z) shows the bare name
   binds the LIBRARY lemma stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, not either MState copy (this file
   Requires lib.Lib.MState without Importing it, so MState's copy is reachable only as MState.Z_to_bv_bv_unsigned).
   This names exactly the constant already used; proof-internal, no statement change. *)
Proof. intros H a n Hr. unfold RNG_W in Hr. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hr. exact Hr. Qed.

(* A range all of whose bytes are visible is a footprint range of RNG_W. *)
Lemma rng_RNG_W : forall (H : word -> bool) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> H (Z_to_bv 64 a) = false) ->
  ExecF.rng (RNG_W H) lo len.
Proof.
  intros H lo len Hlo Hhi Hvis. split; [exact Hlo |]. split; [exact Hhi |].
  intros b j Hb Hj k Hk. unfold woff.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  apply Hvis. lia.
Qed.

(* The visibility fact a call site supplies for one footprint range of a callee contract. *)
Definition range_visible (H : word -> bool) (lo len : Z) : Prop :=
  0 <= lo /\ lo + len <= 2 ^ 64 /\ forall a, lo <= a < lo + len -> H (Z_to_bv 64 a) = false.

Lemma rng_of_visible : forall H lo len, range_visible H lo len -> ExecF.rng (RNG_W H) lo len.
Proof. intros H lo len (A & B & C). exact (rng_RNG_W H lo len A B C). Qed.

(* RNG_W is decided byte by byte, so it meets a Theorem Labs lane's shared runtime contracts' `rng_bytes RNG` premise. *)
Lemma rng_bytes_RNG_W : forall H, RngBytes.rng_bytes (RNG_W H).
Proof.
  intros H b j Hb Hj Hall k Hkj.
  pose proof (Hall k Hkj 0%nat ltac:(lia)) as Hk. rewrite woff_0 in Hk.
  replace (woff (Z_to_bv 64 b) k) with (Z_to_bv 64 (b + Z.of_nat k)); [exact Hk|].
  unfold woff. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* The core's segments (A/AB1v.v) are ctrl's footprint runs' segments (A/Img0.v): both are the image module's
   loaded_segments (a Theorem Labs lane 22:47Z). *)
Lemma tfibsegs_rsegs : AB1v.tfibsegs = rsegs.
Proof. reflexivity. Qed.

(* The core's configuration at a pc (YG0d.cfg_at: YK11.mkst, the FP registers and fcsr from fx, no pending service
   call, no reservation, the segments' rom) is the footprint contracts' start state written with lib/Lib's MS. *)
Lemma cfg_at_MS : forall {fx : YK11.FPState} segs pc regs mem md,
  YG0d.cfg_at segs pc regs mem md =
  mkCfg (MState.MS regs fp_regs (Z_to_bv 64 pc) fp_csr None mem (seg_rom segs)) md.
Proof. reflexivity. Qed.

(* The base and size of each segment of rsegs, computed from the image module (only these projections, not the
   segment bytes). *)
Lemma rsegs_spans : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs =
  [(0x10000, 0x20000); (0x30000, 0x6e000); (0x9e000, 0x3000); (0xa1000, 0x55d000)].
Proof. vm_compute. reflexivity. Qed.

(* A byte inside a segment of segs is visible in every hidden set H that hides no segment byte. *)
Lemma vis_of_seg_span : forall segs H, H_off_segments segs H ->
  forall b sz a, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs) ->
  0 <= a < 2 ^ 64 -> b <= a < b + sz -> H (Z_to_bv 64 a) = false.
Proof.
  intros segs H HH b sz a Hin Ha Hb.
  apply in_map_iff in Hin as (s & Es & Hs). injection Es as <- <-.
  destruct (H (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso.
  pose proof (HH _ E) as Hn. rewrite Z_to_bv_unsigned in Hn. unfold bv_wrap in Hn.
  change (bv_modulus 64) with (2 ^ 64) in Hn. rewrite Z.mod_small in Hn by lia.
  exact (find_segment_none_spec segs a 1 Hn s Hs ltac:(lia)).
Qed.

(* The proof-side loaded segments of image A (lib/A/Img0.v rsegs = images.Asan.M.loaded_segments) are page-rounded
   and contiguous: [0x10000,0x30000) [0x30000,0x9e000) [0x9e000,0xa1000) [0xa1000,0x5fe000), so they tile
   [IMG_LO, IMG_HI) = [0x10000, 0x5fe000); a world never hides a segment byte (w_Hoff), so the whole image is
   visible in every world (a Theorem Labs lane 10-29 00:38Z asked; measured 00:42Z). *)
Lemma img_vis_of_Hoff : forall H, H_off_segments rsegs H ->
  range_visible H ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO).
Proof.
  intros H HH. unfold range_visible, ImgBounds.IMG_LO, ImgBounds.IMG_HI.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split; [lia |]. split; [rewrite P64; lia |]. intros a Ha.
  pose proof (vis_of_seg_span rsegs H HH) as V. rewrite rsegs_spans in V.
  assert (Ha' : 0 <= a < 2 ^ 64) by (rewrite P64; lia).
  destruct (Z_lt_le_dec a 0x30000) as [h1 | h1].
  { apply (V 0x10000 0x20000); [apply in_eq | exact Ha' | lia]. }
  destruct (Z_lt_le_dec a 0x9e000) as [h2 | h2].
  { apply (V 0x30000 0x6e000); [apply in_cons, in_eq | exact Ha' | lia]. }
  destruct (Z_lt_le_dec a 0xa1000) as [h3 | h3].
  { apply (V 0x9e000 0x3000); [apply in_cons, in_cons, in_eq | exact Ha' | lia]. }
  apply (V 0xa1000 0x55d000); [apply in_cons, in_cons, in_cons, in_eq | exact Ha' | lia].
Qed.

(* The same for the hidden set of any world over rsegs (YA0n.w_Hoff). *)
Lemma img_vis_W : forall W : YA0n.world rsegs,
  range_visible (YA0n.w_H W) ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO).
Proof. intros W. exact (img_vis_of_Hoff (YA0n.w_H W) (YA0n.w_Hoff W)). Qed.

(* A sub-range of a visible range is visible. *)
Lemma range_visible_sub : forall H lo len lo' len',
  range_visible H lo len -> lo <= lo' -> 0 <= len' -> lo' + len' <= lo + len ->
  range_visible H lo' len'.
Proof.
  intros H lo len lo' len' (Hlo & Hhi & Hv) Hle Hlen Hsub.
  split; [lia |]. split; [lia |]. intros a Ha. apply Hv. lia.
Qed.

(* The ASan runtime's own data range [RT_LO, RT_HI) = [0x9fad0, 0xa9578) (lib/A/AsanRT.v) lies inside the loaded
   image [0x10000, 0x5fe000), so it is visible in every world for the same reason as the image. A shared runtime
   contract's RT premise is therefore not a call-site duty either. *)
Lemma rt_vis_W : forall W : YA0n.world rsegs,
  range_visible (YA0n.w_H W) AsanRT.RT_LO (AsanRT.RT_HI - AsanRT.RT_LO).
Proof.
  intros W. apply (range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
    [exact (img_vis_W W) | | | ]; unfold AsanRT.RT_LO, AsanRT.RT_HI, ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia.
Qed.
