(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_glue: the facts segment crt1 of image B's LLVMFuzzerTestOneInput needs between
   its runs, its calls and its cut points (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v llvm_b_st_5cc / llvm_b_st_6f0):
   - c1g_evtF_grows / c1g_mem_grows_restrict / c1g_eqv_mkst: a footprint run only grows memory, and the shape of its
     last state (a working branch 02bbf1e30df lib/B/Prog/crtB_glue.v:146-178, by path);
   - c1g_frame: where the fake frame lies (lib/Reusable/YCbq.v:450 frames_bounds at this frame's class);
   - c1g_mode: the mode's two geometry fields are visible, their shadow says addressable, the mode is 4-aligned
     application memory (for a table: the read-only view at its DEC_RO_RD field words, the record's zero shadow at its
     base and the value-4 shadow row of dec_crt_cells; for the fake frame's local: its shadow bytes 0 / 4 of
     dec_b_fsh): leafb.v dec_leafb_plain's mode premises;
   - c1g_garr8_of_bytes: the converse of leafb.v dec_leafb_bytes_garr8;
   - c1g_pok / c1g_dok: the harness's two checks as the segment builds them in s3 / a1 (+0x5cc..+0x5e8) are
     reac_decode_plain_le_c.v plain_ok / reac_decode_c.v decode_ok under dec_b_mode_ok's geometry;
   - c1g_keep_window / c1g_keep_acall: the five kept regions LLVMFuzzerTestOneInput_segX_crt1_cut.v c1_step asks, from a
     call that keeps everything outside its stack window and one block of the caller (a leaf, __asan_memset), and
     from check_round_trip's acall_kept (YCbq.v:824). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning, retries); this file uses the plain
   ones, YM03.v:179-180's lf_lia_orig / lf_nia_orig. *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* ---- crtB_glue.v:146-178, by path, with the prefix crtB_ renamed c1g_ ---- *)
Lemma c1g_eqv_mkst : forall R F pc fc m ro ms,
  Regs6ss.ms_eqv (MS R F pc fc None m ro) ms ->
  ms = @YK11.mkst (YK11.mkFP F fc) (ms_regs ms) pc m ro.
Proof.
  intros R F pc fc m ro [r f p s v c mm rr] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. reflexivity.
Qed.

Lemma c1g_mstepsF_grows : forall RNG ms ms',
  ExecF.mstepsF rsegs RNG ms ms' -> YK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros RNG ms ms' HT. induction HT as [m|m m1 m2 HS HT IH].
  - apply YK1b.mem_grows_refl.
  - eapply YK1b.mem_grows_trans; [|exact IH].
    eapply YI04.step_mem_grows. exact (ExecF.mstepF_step rsegs RNG m m1 HS).
Qed.

Lemma c1g_evtF_grows : forall RNG (P : machine_state -> Prop) ms,
  ExecF.evtF rsegs RNG P ms ->
  ExecF.evtF rsegs RNG (fun ms' => P ms' /\ YK1b.mem_grows (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros RNG P ms (ms' & HT & HP). exists ms'. split; [exact HT|].
  split; [exact HP | exact (c1g_mstepsF_grows RNG ms ms' HT)].
Qed.

Lemma c1g_mem_grows_restrict : forall (H : word -> bool) m m',
  YK1b.mem_grows m m' -> YK1b.mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' HG x Hx. unfold mrestrict in Hx |- *.
  destruct (H x); [exact Hx | exact (HG x Hx)].
Qed.

Section C1Glue. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws decodesegsB0 B.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation RNGW W := (LCK.RNG_W (world segs) (@w_H segs) W).

(* ---- the fake frame ---- *)
Lemma c1g_frame : forall cx ly S W regs mem md k,
  dec_b_core B cx ly S W regs mem md k ->
  4096 <= d_F cx /\ d_F cx + 64 <= YM05.alloc_ceiling /\ in_app (d_F cx) 64 /\
  frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx /\ In (DEC_FCLASS, d_fpos cx) (frames S).
Proof.
  intros cx ly S W regs mem md k Hcore.
  destruct Hcore as (HJ & Hfrs & _).
  pose proof HJ as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
  assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
  assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
  assert (FB : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
  destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (Hb1 & Hb2 & Hb3).
  rewrite EFA in Hb1, Hb2, Hb3. rewrite FB in Hb2, Hb3.
  exact (conj Hb1 (conj Hb2 (conj Hb3 (conj EFA Hin0)))).
Qed.

(* ---- the mode's fields ---- *)
Lemma c1g_vis_of_view : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof. intros W mem a v H. exact (dec_leafb_aview_vis W mem a v H). Qed.

(* Two shadow bytes 0 / 4 at the granules of an 8-aligned G make [G + 4, G + 12) addressable. *)
Lemma c1g_range_addr : forall (rd : reader) G,
  G mod 8 = 0 -> rd (SHADOW_OFF + G / 8) = Some 0 -> rd (SHADOW_OFF + G / 8 + 1) = Some 4 ->
  range_addressable rd SHADOW_OFF (G + 4) 8.
Proof.
  intros rd G HG H0 H4 x Hx. unfold shadow_of_addr.
  assert (Hd : G = 8 * (G / 8)) by (pose proof (Z.div_mod G 8 ltac:(lia)); lia).
  destruct (Z_lt_le_dec x (G + 8)) as [Hl | Hr].
  - assert (E : x / 8 = G / 8).
    { symmetry; apply Z.div_unique with (x - G); [left; lia | lia]. }
    rewrite E. exists 0. split; [exact H0 | left; reflexivity].
  - assert (E : x / 8 = G / 8 + 1).
    { symmetry; apply Z.div_unique with (x - G - 8); [left; lia | lia]. }
    rewrite E. replace (SHADOW_OFF + (G / 8 + 1)) with (SHADOW_OFF + G / 8 + 1) by lia.
    exists 4. split; [exact H4|]. right. split; [|lia].
    assert (Ex : x mod 8 = x - G - 8) by (symmetry; apply Z.mod_unique with (G / 8 + 1); [left; lia | lia]). lia.
Qed.

(* For a table at T (the pointer row gives mode = T): the eight field bytes are DEC_RO_RD bytes, which the read-only
   view (c1_rom_core) shows as the image's, so they are visible; the shadow granule at T is 0 by the record's
   zero-shadow fact (dec_tab_zshadow_rd), the one at T + 8 is 4 by its constant row. *)
Lemma c1g_mode : forall cx ly S W regs mem md k mode nch ns,
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_b_rom cx ->
  dec_b_core B cx ly S W regs mem md k ->
  dec_b_mode_ok cx W mem mode nch ns -> dec_b_fsh cx (aview segs (w_H W) mem) 0 4 ->
  0 < mode /\ mode + 12 <= YM05.alloc_ceiling /\ mode mod 4 = 0 /\ in_app mode 12 /\
  (forall a, mode + 4 <= a < mode + 12 -> w_H W (Z_to_bv 64 a) = false) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (mode + 4) 8.
Proof.
  intros cx ly S W regs mem md k mode nch ns HC HO HE HR Hcore (Hsrc & _ & _ & _ & _) (_ & H4 & H5 & _).
  pose proof (c1g_frame cx ly S W regs mem md k Hcore) as (HF4096 & HFc & HFapp & _ & _).
  pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFal & HFpres & _).
  pose proof (proj1 HJ) as HAR.
  pose proof (c1_rom_core B cx ly S W regs mem md k HO HE HR Hcore) as HRO.
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  (* the common shape: an 8-aligned mode with its two shadow bytes 0 / 4 and its eight field bytes visible *)
  assert (GEN : forall g, 0 < g -> g + 12 <= YM05.alloc_ceiling -> g mod 8 = 0 ->
    aview segs (w_H W) mem (SHADOW_OFF + g / 8) = Some 0 ->
    aview segs (w_H W) mem (SHADOW_OFF + g / 8 + 1) = Some 4 ->
    (forall i, 0 <= i < 8 -> w_H W (Z_to_bv 64 (g + 4 + i)) = false) ->
    in_app g 12 ->
    0 < g /\ g + 12 <= YM05.alloc_ceiling /\ g mod 4 = 0 /\ in_app g 12 /\
    (forall a, g + 4 <= a < g + 12 -> w_H W (Z_to_bv 64 a) = false) /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF (g + 4) 8).
  { intros g Hm0 Hmc Hm8 S0 S4 Vis Happ.
    split; [exact Hm0|]. split; [exact Hmc|]. split; [pose proof (Z.div_mod g 8 ltac:(lia)); lia|].
    split; [exact Happ|].
    split; [intros a Ha; replace a with (g + 4 + (a - (g + 4))) by lia; apply Vis; lia|].
    apply c1g_range_addr; [exact Hm8 | exact S0 | exact S4]. }
  destruct (c1_mode_rows B HC) as (R4 & R5 & R6 & Z44b & Z96b & Z48b).
  destruct (c1_tab_zshadow B HC ly) as (Z44a & Z96a & Z48a).
  (* a table at T: the pointer word gives mode = T *)
  assert (TAB : forall q t, 0 <= t < 2 ^ 64 ->
    (forall l, In (z8 (ANum q) t) (as_const B l)) ->
    rdword (aview segs (w_H W) mem) q = Some mode -> mode = t).
  { intros q t Ht Rq Hq.
    assert (Hw : rdword (aview segs (w_H W) mem) q = Some t).
    { eapply rdword_cell; [lia|].
      exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ (Rq ly)). }
    rewrite Hw in Hq. injection Hq as Hq. symmetry. exact Hq. }
  assert (TABF : forall t, t = 0x20d60 \/ t = 0x20da0 \/ t = 0x20d80 ->
    dec_tab_zshadow_at B t ->
    (forall l, In (z1 (ANum (AsanCells.shadow_addr (t + 8))) 4) (as_const B l)) ->
    0 < t /\ t + 12 <= YM05.alloc_ceiling /\ t mod 4 = 0 /\ in_app t 12 /\
    (forall a, t + 4 <= a < t + 12 -> w_H W (Z_to_bv 64 a) = false) /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF (t + 4) 8).
  { intros t Ht Za Zb.
    assert (Ht0 : 4096 <= t /\ t + 12 <= kLowShadowBeg /\ t mod 8 = 0)
      by (unfold kLowShadowBeg; destruct Ht as [-> | [-> | ->]]; (split; [lia | split; [lia | reflexivity]])).
    destruct Ht0 as (Ht0 & Htl & Ht8).
    unfold kLowShadowBeg in Htl.
    apply GEN; [lia | lia | exact Ht8 | | | |].
    - pose proof (dec_tab_zshadow_rd B ly S W mem md t HAR Ht8 Za) as V.
      unfold AsanCells.shadow_addr, AsanCells.ASAN_K in V.
      unfold SHADOW_OFF. rewrite Z.add_comm. rewrite V. reflexivity.
    - pose proof (c1_cell_view B ly S W mem md (AsanCells.shadow_addr (t + 8)) 1 4 0 HAR (Zb ly) ltac:(lia)) as V.
      cbn [Z.of_nat] in V. rewrite Z.add_0_r in V. unfold AsanCells.shadow_addr, AsanCells.ASAN_K in V.
      assert (E8 : (t + 8) / 8 = t / 8 + 1) by (symmetry; apply Z.div_unique with 0; [left; lia | pose proof (Z.div_mod t 8 ltac:(lia)); lia]).
      rewrite E8 in V. unfold SHADOW_OFF. replace (2147450880 + t / 8 + 1) with (t / 8 + 1 + 2147450880) by lia.
      rewrite V. reflexivity.
    - intros i Hi.
      assert (Hin : dec_in_ro_rd (t + 4 + i)) by (apply (c1_tab_ro t); [exact Ht | lia]).
      destruct (dec_ro_rd_rom_clean (t + 4 + i) Hin) as (_ & b & Hb).
      pose proof (HRO (t + 4 + i) Hin) as V. rewrite Hb in V. cbn [option_map] in V.
      exact (c1g_vis_of_view W mem _ _ V).
    - unfold in_app, kLowShadowBeg. split; [lia | left; lia]. }
  destruct Hsrc as [Hq | [Hq | [Hq | Hloc]]].
  - assert (E : mode = 0x20d60) by (apply (TAB (decodeb_obj 4%nat)); [lia | exact R4 | exact Hq]).
    subst mode. exact (TABF 0x20d60 (or_introl eq_refl) Z44a Z44b).
  - assert (E : mode = 0x20da0) by (apply (TAB (decodeb_obj 5%nat)); [lia | exact R5 | exact Hq]).
    subst mode. exact (TABF 0x20da0 (or_intror (or_introl eq_refl)) Z96a Z96b).
  - assert (E : mode = 0x20d80) by (apply (TAB (decodeb_obj 6%nat)); [lia | exact R6 | exact Hq]).
    subst mode. exact (TABF 0x20d80 (or_intror (or_intror eq_refl)) Z48a Z48b).
  - subst mode.
    assert (HF8 : d_F cx mod 8 = 0) by (pose proof (Z.div_mod (d_F cx) 32 ltac:(lia)); pose proof (Z.div_mod (d_F cx) 8 ltac:(lia)); lia).
    assert (EFd : (d_F cx + 32) / 8 = d_F cx / 8 + 4)
      by (symmetry; apply Z.div_unique with 0; [left; lia | pose proof (Z.div_mod (d_F cx) 8 ltac:(lia)); lia]).
    apply GEN; [lia | lia | rewrite Z.add_mod by lia; rewrite HF8; reflexivity | | | |].
    + rewrite EFd. unfold d_SH, shadow_addr in H4. replace (SHADOW_OFF + (d_F cx / 8 + 4)) with (SHADOW_OFF + d_F cx / 8 + 4) by lia.
      exact H4.
    + rewrite EFd. unfold d_SH, shadow_addr in H5. replace (SHADOW_OFF + (d_F cx / 8 + 4) + 1) with (SHADOW_OFF + d_F cx / 8 + 5) by lia.
      exact H5.
    + intros i Hi. exact (proj1 (HFpres (d_F cx + 32 + 4 + i) ltac:(lia))).
    + apply (in_app_sub (d_F cx) 64 (d_F cx + 32) 12 HFapp); lia.
Qed.

(* ---- a byte list of the raw memory is a garr8 array of the view where nothing is hidden ---- *)
Lemma c1g_garr8_of_bytes : forall (W : world segs) mem p (bs : list byte),
  Mem.bytes_at rsegs mem p bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> w_H W (Z_to_bv 64 (p + i)) = false) ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros W mem p bs (H0 & Ht & Hb) Hvis j Hj. rewrite length_map in Hj.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth. split.
  - intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite <- (dec_leafb_mrd W mem (p + Z.of_nat j) (Hvis (Z.of_nat j) ltac:(lia))).
    transitivity (nth_error bs j); [exact (Hb j Hj)|]. rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj). f_equal.
    symmetry. exact (dec_leafb_le_byte1 (nth j bs (Z_to_bv 8 0))).
  - pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* ---- the regions a call keeps ---- *)
Lemma c1g_body_len : forall cx, d_n cx = Z.of_nat (length (d_pl cx)) ->
  Z.of_nat (length (d_body cx)) = dec_b_len (d_n cx).
Proof.
  intros cx Hn. unfold d_body, dec_b_len, dec_b_u. rewrite length_skipn.
  rewrite Nat2Z.inj_sub_max. rewrite Z2Nat.id by lia. lia.
Qed.

(* exit_defs.v:54-73 ex_perm_twice (commit 44e7264cb0a), copied: no block occurs twice in a list the live blocks
   are a permutation of. *)
Lemma c1g_perm_twice : forall ly S W mem md l1 l2 x,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros ly S W mem md l1 l2 x HAR HP H1 H2.
  apply in_split in H1 as (a1 & a2 & E1). apply in_split in H2 as (c1 & c2 & E2). subst l1 l2.
  assert (HP2 : Permutation (ablocks B ly S) (x :: x :: ((a1 ++ a2) ++ c1) ++ c2)).
  { eapply Permutation_trans; [exact HP|].
    eapply Permutation_trans. { apply Permutation_app; [apply Permutation_sym; apply (Permutation_middle a1 a2 x) | apply Permutation_refl]. }
    change ((x :: a1 ++ a2) ++ c1 ++ x :: c2) with (x :: ((a1 ++ a2) ++ (c1 ++ x :: c2))).
    apply perm_skip.
    replace ((a1 ++ a2) ++ (c1 ++ x :: c2)) with (((a1 ++ a2) ++ c1) ++ x :: c2) by (first [rewrite app_assoc; reflexivity | rewrite <- app_assoc; reflexivity]).
    change (x :: ((a1 ++ a2) ++ c1) ++ c2) with (x :: (((a1 ++ a2) ++ c1) ++ c2)).
    apply Permutation_sym. apply (Permutation_middle ((a1 ++ a2) ++ c1) c2 x). }
  assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
  destruct x as [b m].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hx) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (sep_blocks_perm segs B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos m ltac:(lia)). lia.
Qed.

(* The numbers and the blocks every keep lemma reads at a cut point of crt1. *)
Lemma c1g_layout : forall cx ly S W regs mem md k res out nch ns,
  dec_b_core B cx ly S W regs mem md k ->
  Permutation (ablocks B ly S)
    (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]) ->
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  (d_n cx = 0 \/ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  YM05.alloc_ceiling + 32768 <= d_sp0 cx /\ d_sp0 cx - 240 <= d_sp1 cx /\ d_sp0 cx <= 2 ^ 47 /\
  In (res, dec_b_len (d_n cx)) (ablocks B ly S) /\ In (out, dec_b_olen nch ns) (ablocks B ly S) /\
  4096 <= out /\ out + req_size (dec_b_olen nch ns) <= YM05.alloc_ceiling /\
  in_app out (req_size (dec_b_olen nch ns)) /\
  4096 <= res /\ res + req_size (dec_b_len (d_n cx)) <= YM05.alloc_ceiling /\
  (res + req_size (dec_b_len (d_n cx)) <= out \/ out + req_size (dec_b_olen nch ns) <= res) /\
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     0 <= d_p cx + i < YM05.alloc_ceiling /\
     ~ (out <= d_p cx + i < out + req_size (dec_b_olen nch ns))) /\
  zdisjoint (out, req_size (dec_b_olen nch ns)) (d_F cx, 64).
Proof.
  intros cx ly S W regs mem md k res out nch ns Hcore HP Hn Hpay.
  pose proof (c1g_frame cx ly S W regs mem md k Hcore) as (HF4096 & HFc & HFapp & EFA & Hin0).
  pose proof Hcore as (HJ & _ & _ & _ & _ & Hsp1r & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (HSTK : DEC_LLVMF_STK = 32768) by reflexivity.
  set (base := ablocks B (d_ly cx) (d_S cx)) in *.
  set (len := dec_b_len (d_n cx)) in *. set (olen := dec_b_olen nch ns) in *.
  assert (P2 : Permutation (ablocks B ly S) ((res, len) :: (out, olen) :: base)).
  { eapply Permutation_trans; [exact HP|]. apply (Permutation_app_comm base [(res, len); (out, olen)]). }
  assert (Hr : In (res, len) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | left; reflexivity]).
  assert (Ho : In (out, olen) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | right; left; reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Ho) as (_ & Ho4096 & Hoc & Hoapp & _ & _ & Hon).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hr) as (_ & Hr4096 & Hrc & _ & _ & _ & Hrn).
  pose proof (sep_blocks_perm segs B LAWS ly S W mem md _ _ _ HAR P2) as Hro.
  unfold zdisjoint, block_rng in Hro. cbn [fst snd] in Hro.
  pose proof (sep_block_frame segs B LAWS ly S W mem md out olen DEC_FCLASS (d_fpos cx) HAR Ho Hin0) as Hof.
  rewrite EFA in Hof. change (fs_frame_bytes DEC_FCLASS) with 64 in Hof.
  split; [unfold d_sp0 in *; lia|]. split; [lia|]. split; [unfold d_sp0 in *; lia|].
  split; [exact Hr|]. split; [exact Ho|]. split; [exact Ho4096|]. split; [exact Hoc|]. split; [exact Hoapp|].
  split; [exact Hr4096|]. split; [exact Hrc|]. split; [lia|].
  split; [| exact Hof].
  intros i Hi. destruct Hpay as [H0 | Hinp]; [lia|].
  assert (Hinp' : In (d_p cx, d_n cx) (ablocks B ly S))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; left; exact Hinp]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (d_p cx) (d_n cx) HAR Hinp') as (_ & Hp4096 & Hpc & _ & _ & _ & Hpn).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as [Hq1 Hq2].
  assert (Hne : (d_p cx, d_n cx) <> (out, olen)).
  { intros E. apply (c1g_perm_twice ly S W mem md base ([(res, len)] ++ [(out, olen)]) (out, olen) HAR HP).
    - rewrite <- E. exact Hinp.
    - right. left. reflexivity. }
  pose proof (sep_blocks segs B LAWS ly S W mem md (d_p cx) (d_n cx) out olen HAR Hinp' Ho Hne) as Hpo.
  unfold zdisjoint in Hpo. cbn [fst snd] in Hpo. lia.
Qed.

Lemma c1g_keep_window : forall cx ly S W regs mem md k res out nch ns mem2,
  dec_b_core B cx ly S W regs mem md k ->
  Permutation (ablocks B ly S)
    (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]) ->
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  (d_n cx = 0 \/ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
     ~ (out <= a < out + req_size (dec_b_olen nch ns)) -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) /\
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a /\
     apresent (w_H W) mem2 a) /\
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) /\
  (forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
     aview segs (w_H W) mem2 (res + i) = aview segs (w_H W) mem (res + i)) /\
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     aview segs (w_H W) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)).
Proof.
  intros cx ly S W regs mem md k res out nch ns mem2 Hcore HP Hn Hpay K PR.
  pose proof (c1g_frame cx ly S W regs mem md k Hcore) as (HF4096 & HFc & HFapp & EFA & Hin0).
  pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpres & _).
  destruct (c1g_layout cx ly S W regs mem md k res out nch ns Hcore HP Hn Hpay) as
    (Hsp0 & Hsp1 & H47 & _ & _ & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
  pose proof (c1g_body_len cx Hn) as Hbl.
  pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(unfold dec_b_len; lia)) as [Hq1 Hq2].
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  unfold zdisjoint in Hof. cbn [fst snd] in Hof. unfold ESTACK in *.
  split; [|split; [|split; [|split]]].
  - intros a Ha. apply K; lia.
  - intros a Ha. split; [apply K; lia | apply PR; exact (HFpres a Ha)].
  - intros a Ha. unfold d_SH, shadow_addr, SHADOW_OFF in Ha.
    assert (Hd : d_F cx / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hoapp.
    apply K; lia.
  - intros i Hi. apply K; lia.
  - intros i Hi. destruct (Hpo i Hi) as (Hp1 & Hp2). apply K; lia.
Qed.

Lemma c1g_keep_acall : forall cx ly S W regs mem md k res out nch ns W2 mem2,
  dec_b_core B cx ly S W regs mem md k ->
  Permutation (ablocks B ly S)
    (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]) ->
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  (d_n cx = 0 \/ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  @acall_kept rc segs B ly S W mem W2 mem2 (d_sp1 cx - DEC_CRT_STK) (d_sp1 cx) (fun _ => False) ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) /\
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a /\
     apresent (w_H W2) mem2 a) /\
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) /\
  (forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
     aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) mem (res + i)) /\
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)) /\
  (forall i, 0 <= i < req_size (dec_b_olen nch ns) ->
     aview segs (w_H W2) mem2 (out + i) = aview segs (w_H W) mem (out + i)).
Proof.
  intros cx ly S W regs mem md k res out nch ns W2 mem2 Hcore HP Hn Hpay HK.
  pose proof (c1g_frame cx ly S W regs mem md k Hcore) as (HF4096 & HFc & HFapp & EFA & Hin0).
  pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpres & _).
  pose proof (proj1 HJ) as HAR.
  destruct (c1g_layout cx ly S W regs mem md k res out nch ns Hcore HP Hn Hpay) as
    (Hsp0 & Hsp1 & H47 & Hr & Ho & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
  pose proof (c1g_body_len cx Hn) as Hbl.
  pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(unfold dec_b_len; lia)) as [Hq1 Hq2].
  pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (FB : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
  assert (HCS : DEC_CRT_STK = 160 + ASTACK) by reflexivity. unfold ASTACK in HCS.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply K1; lia.
  - intros a Ha.
    assert (Hv : aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
    { apply (K4 DEC_FCLASS (d_fpos cx) a Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, FB; lia | intros []]. }
    split; [exact Hv|].
    apply (apresent_transfer segs (w_H W) (w_H W2) mem mem2 a); [lia | | exact Hv | exact (HFpres a Ha)].
    apply (frm_img segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) a HAR Hin0). rewrite EFA, FB. lia.
  - intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Hin0); [right; unfold in_zr; cbn [fst snd]; rewrite EFA, FB; unfold d_SH in Ha; change (64 / 8) with 8; lia | intros []].
  - intros i Hi. apply (K2 res (dec_b_len (d_n cx)) i Hr); [lia | intros []].
  - intros i Hi. destruct Hpay as [H0 | Hinp]; [lia|].
    assert (Hinp' : In (d_p cx, d_n cx) (ablocks B ly S))
      by (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; left; exact Hinp]).
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as [Hp1 Hp2].
    apply (K2 (d_p cx) (d_n cx) i Hinp'); [lia | intros []].
  - intros i Hi. apply (K2 out (dec_b_olen nch ns) i Ho); [lia | intros []].
Qed.

End C1Glue.

(* ---- the harness's two checks ---- *)
Lemma c1g_prod : forall nch ns, 0 < nch <= 127 -> 0 < ns <= 127 -> dec_b_prod nch ns = nch * ns.
Proof.
  intros nch ns H1 H2. unfold dec_b_prod.
  rewrite (Z.mod_small nch) by lia. rewrite (Z.mod_small ns) by lia. apply Z.mod_small. nia.
Qed.

Lemma c1g_pok : forall len bs nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  (CInsp.inspect_wf len bs && ((0 <? nch) && (0 <? ns)) && (dec_b_prod nch ns <? 481))%bool =
  CPlain.plain_ok len bs nch ns.
Proof.
  intros len bs nch ns Hn Hs. unfold CPlain.plain_ok.
  destruct (CInsp.inspect_wf len bs); cbn [andb]; [|reflexivity].
  destruct (Z.ltb_spec 0 nch) as [Pn|Pn]; cbn [andb]; [|reflexivity].
  destruct (Z.ltb_spec 0 ns) as [Ps|Ps]; cbn [andb]; [|reflexivity].
  rewrite (c1g_prod nch ns) by lia.
  destruct (Z.ltb_spec (nch * ns) 481); destruct (Z.leb_spec (nch * ns) 480); lia || reflexivity.
Qed.

Lemma c1g_dok : forall len bs nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  (CInsp.inspect_wf len bs && ((0 <? nch) && (0 <? ns)) && (dec_b_prod nch ns <? 481) && (nch mod 2 =? 0))%bool =
  CDec.decode_ok len bs nch ns.
Proof.
  intros len bs nch ns Hn Hs. unfold CDec.decode_ok.
  destruct (CInsp.inspect_wf len bs); cbn [andb]; [|reflexivity].
  destruct (Z.ltb_spec 0 nch) as [Pn|Pn]; cbn [andb]; [|reflexivity].
  destruct (nch mod 2 =? 0); cbn [andb]; [| rewrite !andb_false_r; reflexivity].
  destruct (Z.ltb_spec 0 ns) as [Ps|Ps]; cbn [andb]; [|reflexivity].
  rewrite (c1g_prod nch ns) by lia.
  destruct (Z.ltb_spec (nch * ns) 481); destruct (Z.leb_spec (nch * ns) 480); lia || reflexivity.
Qed.
