(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem Mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_kit Stdio_kit AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import F_fmt_fp_lib RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AHarnessU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Lemma le8_of_bytesA : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma word_of_wr_at : forall m A, wr_at asegs m A 8 -> 0x665000 <= A -> exists w : Z, 0 <= w < 2^64 /\ bytes_at asegs m A (le8 (Z_to_bv 64 w)).
Proof.
  intros m A W HA. destruct (rw_cells_of_wr_at asegs m A 8 W (no_image_asan A (A + 8) HA) ltac:(lia)) as (bs & HL & C).
  exists (bv_unsigned (le_bytes_to_word bs)). split; [pose proof (bv_unsigned_in_range 64 (le_bytes_to_word bs)) as R; unfold bv_modulus in R; exact R|].
  rewrite Z_to_bv_bv_unsigned. rewrite le8_of_bytesA by exact HL.
  pose proof (rw_cells_bytes_at _ _ _ _ C) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma wr_at_subF : forall m A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> wr_at asegs m A' n'.
Proof. intros m A n A' n' (H0 & H1 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma uchain_exists : forall m top pc k prev frame, 0x665000 <= prev - 16 -> top <= 2^47 ->
  wr_at asegs m (prev - 16) (top - (prev - 16)) -> exists tr, uchain m top pc prev frame k tr.
Proof.
  intros m top pc k prev frame H0 HT W.
  remember (Z.to_nat (top - prev)) as n eqn:En. revert k prev frame H0 W En.
  induction n as [n IH] using lt_wf_ind. intros k prev frame H0 W En.
  destruct (Z_lt_dec prev frame) as [C1|C1]; [|exists []; apply uc_stop; lia].
  destruct (Z_lt_dec frame (top - 16)) as [C2|C2]; [|exists []; apply uc_stop; lia].
  destruct (Z.eq_dec (frame mod 8) 0) as [C3|C3]; [|exists []; apply uc_stop; lia].
  destruct (Nat.eq_dec k 0) as [C4|C4]; [exists []; apply uc_stop; lia|].
  destruct (word_of_wr_at m (frame - 16) ltac:(eapply wr_at_subF; [exact W| lia| lia| lia]) ltac:(lia)) as (fp & Rfp & Bfp).
  destruct (word_of_wr_at m (frame - 8) ltac:(eapply wr_at_subF; [exact W| lia| lia| lia]) ltac:(lia)) as (ra & Rra & Bra).
  destruct (Z_lt_dec ra 4096) as [C5|C5].
  - exists []. eapply uc_lowpc; [lia| lia| exact C3| lia| exact Bfp| exact Bra| lia].
  - destruct (IH (Z.to_nat (top - frame)) ltac:(lia) (if ra =? pc then k else Nat.pred k) frame fp ltac:(lia)
                 ltac:(eapply wr_at_subF; [exact W| lia| lia| lia]) eq_refl) as (tr & Htr).
    exists ((if ra =? pc then [] else [ra]) ++ tr). eapply uc_step; [lia| lia| exact C3| lia| exact Bfp| exact Bra| lia| lia| exact Htr].
Qed.

(* [comment removed for export] *)
Lemma uchain_length : forall m top pc prev frame k tr, uchain m top pc prev frame k tr -> (length tr <= k)%nat.
Proof.
  intros m top pc prev frame k tr H. induction H as [|? ? ? ? ? ? ? ? ? ? ? ? ?|prev frame k fp ra tr ? ? ? ? ? ? ? ? ? IH].
  - cbn. lia.
  - cbn. lia.
  - destruct (ra =? pc); cbn [app length]; lia.
Qed.

(* [comment removed for export] *)
Lemma stk_wmonoF : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> 0x665000 <= lo -> hi <= 2^64 -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) WM Hlo Hhi. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (WM _ Hw) as Hw'. split; [exact Hw'|].
  rewrite ref_wview_overlay in Hw' by (unfold wa; rewrite unsigned_lit by lia; lia).
  destruct (m' (wa a)) as [b|] eqn:Hm; [|contradiction]. exists b. rewrite ref_mrd_overlay by (unfold wa; rewrite unsigned_lit by lia; lia). exact Hm.
Qed.
Lemma wr_at_wmonoF : forall m m' A n, wr_at asegs m A n -> wmono asegs m m' -> wr_at asegs m' A n.
Proof. intros m m' A n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply W. apply H. exact Hi. Qed.
Lemma wr_at_of_stkF : forall m lo hi A n, stk asegs m lo hi -> lo <= A -> A + n <= hi -> 0 <= n -> wr_at asegs m A n.
Proof. intros m lo hi A n (H0 & H1 & H) H2 H3 H4. split; [lia|]. split; [lia|]. intros i Hi. apply (H (A + i)). lia. Qed.
Lemma wr_at_joinF : forall m A n B k, wr_at asegs m A n -> wr_at asegs m B k -> B = A + n -> 0 <= n -> 0 <= k -> wr_at asegs m A (n + k).
Proof.
  intros m A n B k (A0 & A1 & HA) (B0 & B1 & HB) E Hn Hk. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z_lt_dec i n) as [L|L]; [apply HA; lia|]. replace (A + i) with (B + (i - n)) by lia. apply HB. lia.
Qed.
(* [comment removed for export] *)
Lemma rclean_munchF : forall W m m' r, rclean m r -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W (shad (r_rlo r)) (shad (r_rhi r) - shad (r_rlo r)) -> rclean m' r.
Proof. intros W m m' r [SH LT] MU WM D. split; [eapply shclean_transport; eauto| exact LT]. Qed.
(* [comment removed for export] *)
Lemma cells_byteF : forall m A cs i b, rw_cells asegs m A cs -> nth_error (cells_bytes cs) (Z.to_nat i) = Some b -> 0 <= i ->
  0x665000 <= A -> m (wa (A + i)) = Some b.
Proof.
  intros m A cs i b C Hn Hi HA. pose proof (rw_cells_bytes_at _ _ _ _ C) as (B0 & B1 & B).
  assert (Hl : (Z.to_nat i < length (cells_bytes cs))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  specialize (B (Z.to_nat i) Hl). rewrite Z2Nat.id in B by lia. rewrite Hn in B.
  rewrite ref_mrd_overlay in B by (unfold wa; rewrite unsigned_lit by lia; lia). exact B.
Qed.

(* [comment removed for export] *)
Lemma unpoisoned_of_zeroF : forall m lo hi sb,
  0 <= lo -> lo < hi -> hi <= 2^64 -> sb = ASHOFF + lo / 8 ->
  (forall i, 0 <= i < (hi + 7) / 8 - lo / 8 -> m (wa (sb + i)) = Some (Z_to_bv 8 0)) ->
  unpoisoned m lo hi.
Proof.
  intros m lo hi sb H0 H1 H2 Hsb HZ. split; [lia|]. split; [lia|]. intros G _ HG1 HG2.
  exists (Z_to_bv 8 0). split.
  - replace (ASHOFF + G) with (sb + (G - lo / 8)) by lia. apply HZ. Z.div_mod_to_equations. lia.
  - left. reflexivity.
Qed.

Lemma sval0_byteF : forall b : byte, sval b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  change (256 `div` 2) with 128 in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_cells_of_rclean : forall m r X k, rclean m r -> r_lo r <= X -> X + 8 * k <= r_hi r -> X mod 8 = 0 -> 0 <= k ->
  rw_cells asegs m (Z.shiftr X 3 + 2147450880) [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m r X k [((U0 & U1 & U) & (H1 & H2 & H3 & H4 & H5 & H6) & (W0 & W1 & W) & AB) LT] HX1 HX2 HX3 Hk.
  assert (EX : Z.shiftr X 3 = X / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Z8 : forall i, 0 <= i < k -> m (wa (X / 8 + 2147450880 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (U (X / 8 + i) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (b & Hb & Hg).
    replace (Z.min (8 * (X / 8 + i) + 8) (r_hi r) - 8 * (X / 8 + i)) with 8 in Hg by (Z.div_mod_to_equations; lia).
    unfold gran_ok in Hg. assert (Hs : sval b = 0) by lia. rewrite (sval0_byteF b Hs) in Hb.
    unfold ASHOFF in Hb. replace (X / 8 + 2147450880 + i) with (2147450880 + (X / 8 + i)) by lia. exact Hb. }
  rewrite EX. split; [split|].
  - cbn. rewrite repeat_length. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [Z.div_mod_to_equations; lia|]. split; [rewrite repeat_length; unfold KEND in *; Z.div_mod_to_equations; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by lia.
    rewrite ref_mrd_overlay by (unfold wa; rewrite unsigned_lit by (unfold KEND in *; Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia).
    apply (Z8 (Z.of_nat i)). lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. rewrite Z2Nat.id by lia. split; [Z.div_mod_to_equations; lia|].
    split; [unfold KEND in *; Z.div_mod_to_equations; lia|]. intros i Hi.
    rewrite !shad_div in W. unfold ASHOFF in W.
    specialize (W (X / 8 - r_rlo r / 8 + i) ltac:(Z.div_mod_to_equations; lia)).
    match type of W with wview _ _ (wa ?a) <> None => replace a with (X / 8 + 2147450880 + i) in W by lia end. exact W.
Qed.

(* [comment removed for export] *)
Lemma aheap_pres_W_stkF : forall (CI : list (Z * Z)) LB SP W m m' lo hi, aheap_pres_W CI LB SP W m m' -> stk asegs m lo hi -> SP <= lo -> hi <= 2^47 ->
  (forall a, lo <= a < hi -> outside W a) -> stk asegs m' lo hi.
Proof.
  intros CI LB SP W m m' lo hi PW (H0 & H1 & H) HS HH HO. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. destruct (PW a ltac:(lia) ltac:(left; lia) (HO a Ha)) as [E Wv].
  split; [exact (Wv Hw)|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Section Fk.
  Variable AI : AMallocIface.
  (* [comment removed for export] *)
  Lemma fresh_fake_not_client : forall L RNG st c F N LB m SP a, AHEAP AI L RNG st (mkABlock (ABFake c) F N :: LB) m ->
    ablk F (F + N) -> ATOP <= SP -> aclient_addr (aci AI) LB SP a -> ~ (F <= a < F + N).
  Proof.
    intros L RNG st c F N LB m SP a AH B1 HS Hc Ha.
    pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). atop_facts.
    pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. apply NoDup_cons_iff in ND as [NI _].
    destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    - assert (NE : mkABlock (ABFake c) F N <> b) by (intros E; subst b; exact (NI Hb)).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (or_introl eq_refl) (or_intror Hb) NE) as D. cbn [ab_addr ab_size] in D. lia.
    - assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c' & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (or_intror Hb')) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      pose proof (shad_band1 a' ltac:(lia) ltac:(unfold KEND; lia)) as SB.
      exact (ablk_clear_band _ _ _ B1 SB Ha).
  Qed.
End Fk.

(* [comment removed for export] *)
Definition fuzz_oneU_postW (AI : AMallocIface) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : APS) (LB : list ablock) (lo : Z) (m : amem)
    (r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem) (LB' : list ablock),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ r = 0
    /\ mem_inv asegs m' /\ frm0 fc'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ harness_pres (aci AI) LB (bv_unsigned sp) m m'
    /\ astk_shadow_pres (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG' (aps_m s') LB' m'
    /\ harness_invA m' /\ client_static s' LB' m'
    /\ aps_rest s' = aps_rest s
    /\ LB' = LB /\ aps_cl s' = aps_cl s
    /\ AFRESH (aps_m s') /\ dk (aps_m s') <= dk (aps_m s) + 8.

End CANSEC1.
