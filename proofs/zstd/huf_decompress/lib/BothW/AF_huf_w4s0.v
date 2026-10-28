(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4m AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S0.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Notation W4F' mm fr mid l256 l296 l336 :=
    (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm fr mid l256 l296 l336).

  Definition AW4_S0C : Z := 564432.

  Definition w4s0c_goal : Prop :=
    forall (l1 l2 l3 : Z) (w0 w1 w2 w3 w5 w6 w7 : word) (j1 j2 j3 j4 rest : list byte) (mm : amem)
           (x1 x5 x6 x7 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    W4F' mm [C8 w0; C8 w1; C8 w2; C8 w3; C8 (Z_to_bv 64 seg); C8 w5; C8 w6; C8 w7; C8 (Z_to_bv 64 (DST + seg));
             C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + dcap))]
            [CB 40 j1; CB 112 rest] [CB 40 j4] [CB 40 j3] [CB 40 j2] ->
    0 <= l1 < 65536 -> 0 <= l2 < 65536 -> 0 <= l3 < 65536 -> 6 + l1 + l2 + l3 <= n -> 6 <= dcap ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 (6 + l1 + l2 + l3)) x9 x10 (Z_to_bv 64 (SS + 6))
               (Z_to_bv 64 l1) x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + 2 * seg)) (Z_to_bv 64 n)
               (Z_to_bv 64 (SS + 6 + l1 + l2)) (Z_to_bv 64 l3) (Z_to_bv 64 l2) (Z_to_bv 64 (SS + 6 + l1))
               (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + 3 * seg))
               x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_S0C) fc None mm (seg_rom bsegs)).

  Hypothesis W4S0C : w4s0c_goal.
  Ltac w4s_clr := repeat match goal with H : _ |- _ => clear H end.
  Lemma w4s_landm : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
  Proof using. w4s_clr. intros. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small; lia. Qed.
  Lemma w4s_landz : forall x, Z.land x 18446744073709551615 = x mod 2^64.
  Proof using. w4s_clr. intros. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones; lia. Qed.
  Lemma w4s_land3 : forall x, Z.land x 3 = x mod 4.
  Proof using. w4s_clr. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
  Lemma w4s_landle : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
  Proof using. w4s_clr.
    intros a m A M. split; [apply Z.land_nonneg; left; exact A|].
    assert (D : 0 <= Z.ldiff a m) by (rewrite Z.ldiff_land; apply Z.land_nonneg; left; exact A).
    assert (E : Z.land (Z.ldiff a m) (Z.land a m) = 0).
    { apply Z.bits_inj'; intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit a i), (Z.testbit m i); reflexivity. }
    assert (G : Z.lxor (Z.ldiff a m) (Z.land a m) = a).
    { apply Z.bits_inj'; intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec, Z.land_spec.
      destruct (Z.testbit a i), (Z.testbit m i); reflexivity. }
    pose proof (Z.add_nocarry_lxor _ _ E) as F. rewrite G in F. lia.
  Qed.

  Lemma w4s_landev : forall x, 0 <= x < 2^64 -> x mod 2 = 0 -> Z.land x 18446744073709551614 = x.
  Proof using. w4s_clr.
    intros x X E.
    replace 18446744073709551614 with (Z.lxor (Z.ones 64) 1) by reflexivity.
    apply Z.bits_inj'; intros i Hi.
    rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|NZ].
    - rewrite !Z.bit0_odd, Zodd_mod, E. reflexivity.
    - destruct (Z_lt_le_dec i 64) as [Li|Li].
      + rewrite Z.lxor_spec, Z.ones_spec_low by lia. rewrite (Z.bits_above_log2 1 i) by (cbn; lia).
        destruct (Z.testbit x i); reflexivity.
      + assert (LG : Z.log2 x < 64).
        { destruct (Z.eq_dec x 0) as [->|NX]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
        rewrite (Z.bits_above_log2 x i) by lia. reflexivity.
  Qed.
  Lemma w4s_le16 : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
    Z.lor (Z.land (Z.shiftl (bv_unsigned (Z_to_bv 8 a)) 8) 18446744073709551615) (bv_unsigned (Z_to_bv 8 b)) = b + 256 * a.
  Proof using. w4s_clr.
    intros a b A B. rewrite !byte_lit by lia.
    rewrite w4s_landm by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite Z.lor_comm. apply lor_shiftl8_add; lia.
  Qed.
  Lemma w4s_byte : forall k, 0 <= Znth k src < 256.
  Proof using All.
    intros k. unfold Znth. destruct (nth_in_or_default (Z.to_nat k) src 0) as [I|E].
    - exact (proj1 (Forall_forall _ _) BYS _ I).
    - rewrite E. lia.
  Qed.

  Lemma w4s_fs1 : forall (l : list Z) i, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l 0].
  Proof using. w4s_clr. induction l as [|x l IH]; intros i Hi; destruct i as [|i]; cbn in *; first [lia | reflexivity | (apply IH; lia)]. Qed.

  Lemma w4s_rd1 : forall m A (l : list Z) k, bytes_at bsegs m A (map (Z_to_bv 8) l) -> 0 <= k < zlen l ->
    ov_read_bytes bsegs m (Z_to_bv 64 (A + k)) 1 = Some [Z_to_bv 8 (Znth k l)].
  Proof using. w4s_clr.
    intros m A l k H K. change (Z_to_bv 64 (A + k)) with (wa (A + k)).
    rewrite (bytes_at_read bsegs m A _ k 1 H) by (rewrite ?length_map; lia).
    rewrite skipn_map, firstn_map, w4s_fs1 by lia. reflexivity.
  Qed.

  Lemma w4s_rd0 : forall m A (l : list Z), bytes_at bsegs m A (map (Z_to_bv 8) l) -> 0 < zlen l ->
    ov_read_bytes bsegs m (Z_to_bv 64 A) 1 = Some [Z_to_bv 8 (Znth 0 l)].
  Proof using. w4s_clr. intros m A l H K. rewrite <- (w4s_rd1 m A l 0 H) by lia. rewrite Z.add_0_r. reflexivity. Qed.

  Lemma w4s_rsb : forall R0 l0 h0 a0, rng R0 (shad l0) (shlen (h0 - l0 + 7)) -> l0 mod 16 = 0 -> l0 <= a0 < h0 ->
    rng R0 (Z.shiftr a0 3 + AW4_KSB) 1.
  Proof using. w4s_clr.
    intros R0 l0 h0 a0 HR A16 B. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    assert (Q : l0 / 8 <= a0 / 8 /\ a0 / 8 + 1 <= l0 / 8 + shlen (h0 - l0 + 7))
      by (rewrite shlenE; clear - A16 B; Z.div_mod_to_equations; lia).
    replace (a0 / 8 + AW4_KSB) with (shad l0 + (a0 / 8 - l0 / 8)) by (rewrite shad_div; unfold ASHOFF, AW4_KSB; lia).
    eapply rng_sub; [exact HR | lia | lia].
  Qed.
  Lemma w4s_c8 : forall m A pre bs post, rw_cells bsegs m A (pre ++ CB 8 bs :: post) ->
    exists w : word, rw_cells bsegs m A (pre ++ C8 w :: post).
  Proof using. w4s_clr. intros m A pre bs post H.
    apply ABytes.rw_cells_app in H. destruct H as (H1 & H2).
    change (CB 8 bs :: post) with ([CB 8 bs] ++ post) in H2. apply ABytes.rw_cells_app in H2. destruct H2 as (H2 & H3).
    destruct (ABytes.c8_of_CB _ _ _ H2) as (w & H4 & _). exists w.
    apply ABytes.rw_cells_app. split; [exact H1|].
    change (C8 w :: post) with ([C8 w] ++ post). apply ABytes.rw_cells_app. split; [exact H4|]. exact H3.
  Qed.
  Ltac w4pre cs := lazymatch cs with CB 8 _ :: _ => constr:(@nil cell) | ?c :: ?r => let p := w4pre r in constr:(c :: p) end.
  Ltac w4c8 H := repeat (lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let p := w4pre cs in let w := fresh "fw" in let H2 := fresh "F0c" in
    destruct (w4s_c8 m A p _ _ H) as (w & H2); clear H; rename H2 into H; cbn [app] in H end).

  Lemma w4s_sp : 0x10007fff8000 <= SP + -496 /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using All.
  pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
  unfold HUF_DEC_STACK_A in LOS. clear - HL HA LOS LOA SPT. lia.
Qed.
  Lemma w4s_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ DT + 4 + zlen cbs <= DT + DTL
                     /\ (dcap = 0 \/ (AIMG_HI <= DST /\ DST + dcap <= ATOP))
                     /\ (n = 0 \/ (AIMG_HI <= SBL /\ SBL <= SS /\ SS + n <= SBH /\ SBH <= ATOP)).
Proof using All.
  pose proof (AI_block AI L RNG st LB m0 pdt DT DTL AH HDT) as (BD1 & (BD2 & BD3 & BD4 & BD5) & _).
  pose proof (ablk_img _ _ BD2) as I1.
  cbv [DTABLE_BYTES HufHarness.DT_BYTES] in *.
  assert (P2 : 2 ^ tl <= 2 * 2 ^ mtl).
  { destruct (Z_lt_le_dec tl 0) as [Hn|Hn].
    - rewrite (Z.pow_neg_r 2 tl Hn). pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)). lia.
    - replace (2 * 2 ^ mtl) with (2 ^ (mtl + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
  split; [exact I1|]. split; [lia|]. split; [exact BD5|]. split; [lia|]. split.
  - destruct DSTF as [[-> ->]|(pb & HB)]; [left; reflexivity|right].
    pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (_ & (C2 & C3 & C4 & C5) & _).
    split; [exact (ablk_img _ _ C2)|lia].
  - destruct (Z.eq_dec n 0) as [E|E]; [left; exact E|right].
    destruct (SRCB ltac:(lia)) as (p & HB & S1 & S2).
    pose proof (AI_block AI L RNG st LB m0 p SBL (SBH - SBL) AH HB) as (_ & (C2 & C3 & C4 & C5) & _).
    pose proof (ablk_img _ _ C2). lia.
Qed.
  Lemma w4s_d0 : 0 <= DST /\ DST + dcap <= ATOP /\ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST).
Proof using All.
  pose proof (@ATOP_lo rc) as HA.
  destruct DSTF as [[-> ->]|(pb & HB)]; [lia|].
  pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (D1 & (C2 & C3 & C4 & C5) & _).
  unfold ablk, AIMG_HI, KLS in C2. lia.
Qed.
  Lemma w4s_appW : appW DW.
Proof using All.
  pose proof w4s_d0 as (D1 & D2 & D3). pose proof (@ATOP_lo rc) as HA.
  unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; lia.
Qed.
Lemma w4_wr_u8arr : forall m A n, wr_at bsegs m A n -> 0 <= n -> 0x60f000 <= A ->
  exists buf : list Z, u8arr bsegs m A (map (Z_to_bv 8) buf) /\ zlen buf = n.
Proof.
  intros m A n (W0 & W1 & W2) Hn HA.
  assert (WU : forall z, 0 <= z < 2^64 -> bv_unsigned (wa z) = z)
    by (intros z Hz; unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; exact Hz).
  set (f := fun i : nat => match m (wa (A + Z.of_nat i)) with Some b => bv_unsigned b | None => 0 end).
  exists (map f (seq 0 (Z.to_nat n))).
  unfold u8arr, bytes_at, wr_at. rewrite !length_map, length_seq.
  split; [|lia]. split.
  - split; [lia|]. split; [lia|]. intros i Hi.
    rewrite ref_mrd_overlay by (rewrite WU by lia; lia).
    rewrite !nth_error_map, nth_error_seq.
    replace (i <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map]. replace (0 + i)%nat with i by lia.
    specialize (W2 (Z.of_nat i) ltac:(lia)). rewrite ref_wview_overlay in W2 by (rewrite WU by lia; lia).
    unfold f. destruct (m (wa (A + Z.of_nat i))) as [b|] eqn:E; [|contradiction].
    f_equal. symmetry. apply definitions.Z_to_bv_bv_unsigned.
  - split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
Qed.
  Lemma w4s_out : forall m, wmono bsegs m0 m ->
    (DST = 0 /\ dcap = 0) \/ (exists buf, u8arr bsegs m DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap).
Proof using All.
  intros m WM. destruct DSTF as [[-> ->]|(pb & HB)]; [left; split; reflexivity|right].
  pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (D1 & (C2 & C3 & C4 & C5) & R1 & R2 & SDW & W & _).
  pose proof (ablk_img _ _ C2) as I1. unfold AIMG_HI in I1.
  apply w4_wr_u8arr; [eapply wr_at_transport; [exact W | exact WM] | lia | lia].
Qed.
  Lemma w4s_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using All.
  intros mm MU WM. pose proof w4s_sp as SPB.
  destruct DSTF as [[E1 E2] | [pb HBo]].
  - eapply (AI_frame AI _ _ _ _ m0 mm [(lo, SP)]); [exact AH | eapply munch_weaken; [|exact MU] | exact WM |].
    + intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [exact Hx | split; [lia | exact I]].
    + apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
      left. left. lia.
  - eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
    + left. left. lia.
    + right. left. exists (HB pb DST dcap). split; [exact HBo|]. cbn. lia.
Qed.
  Lemma w4s_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using All.
  intros mm MU WM. apply (munch_magreeA DW m0 mm); [exact MU | exact WM |].
  intros a [CA ND]. cbn [outside]. split; [| split; [exact ND | exact I]].
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  destruct CA as [S | [R | [B | (a' & A' & E)]]].
  - lia.
  - destruct R as (iv & IN & R1 & R2). pose proof (AI_aci_img AI iv IN) as HI. unfold ABase.AIMG_HI in HI. lia.
  - destruct B as (b & IN & B1 & B2). pose proof (AI_block_bounds AI _ _ _ _ _ b AH IN) as (BB1 & BB2 & BB3).
    unfold ABase.AIMG_HI in BB1. lia.
  - subst a. unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia.
    assert (A'B : 0 <= a' < 2^47).
    { destruct A' as [A1 | [(iv & IN & R1 & R2) | (cls & A & k & IN & F1 & F2)]].
      - lia.
      - pose proof (AI_aci_img AI iv IN). pose proof (AI_aci_lo AI iv IN). unfold ABase.AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (BB1 & BB2 & BB3). cbn [ab_addr ab_size] in BB1, BB2, BB3.
        unfold ABase.AIMG_HI in *. lia. }
    Z.div_mod_to_equations. lia.
Qed.
  Lemma w4s_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo (SP + -104) -> rw_cells bsegs mm (SP + -104) FRS ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 AW4_EPI) fc None mm (seg_rom bsegs)).
Proof using All.
  intros mm t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra ST FRC MI MU WM.
  pose proof w4s_sp as SPB.
  unfold AW4_EPI.
  do 15 zstep.
  release_frame FRC ST (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  do 15 eexists. exists mm.
  split; [reflexivity|].
  exact (conj MI (conj ST (conj (w4s_magree mm MU WM) (w4s_aheap mm MU WM)))).
Qed.
  Lemma w4s_unp : forall m, munch DW m0 m ->
    unpoisoned m DT (DT + DTL) /\ (0 < n -> unpoisoned m SS (SS + n)).
Proof using All.
  intros m MU.
  pose proof w4s_sp as (S1 & S2 & S3 & S4). pose proof (@ATOP_lo rc) as HA. pose proof (@ATOP_hi rc) as HA2.
  pose proof w4s_d0 as (D1 & D2 & D3).
  pose proof (hb_unpoisoned AI L RNG st LB m0 pdt DT DTL AH HDT) as (U1 & _ & _ & K1 & _).
  unfold ablk, AIMG_HI, KLS in K1.
  split.
  - eapply unpoisoned_munch; [exact U1 | exact MU |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. lia.
  - intros Hn. destruct (SRCB Hn) as (p & HB & B1 & B2).
    pose proof (hb_unpoisoned AI L RNG st LB m0 p SBL (SBH - SBL) AH HB) as (U2 & _ & _ & K2 & _).
    unfold ablk, AIMG_HI, KLS in K2.
    eapply unpoisoned_munch; [eapply unpoisoned_sub; [exact U2 | lia | lia] | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. lia.
Qed.

  Ltac w4at pc := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let b := eval vm_compute in (p =? pc) in lazymatch b with true => idtac end end.
  Ltac w4lit x := lazymatch x with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end.
  Ltac w4cw x := lazymatch x with Z_to_bv _ ?a => w4lit a | sxb (Z_to_bv _ ?a) => w4lit a end.
  Ltac w4closed c := lazymatch c with
    | negb ?c' => w4closed c'
    | bv_ltu ?a ?b => w4cw a; w4cw b
    | bv_lts ?a ?b => w4cw a; w4cw b
    | bv_eqb ?a ?b => w4cw a; w4cw b
    end.
  Ltac w4if := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then ?x else ?y) _ _ _ _) =>
    w4closed c; let v := eval vm_compute in c in lazymatch v with
    | true => change (if c then x else y) with x
    | false => change (if c then x else y) with y end end.
  Ltac w4unimp p := let u := eval vm_compute in (match fetch_word bsegs (Z_to_bv 64 p) with
      Some w => orb (orb (bv_unsigned w =? 3221229683) (bv_unsigned w mod 65536 =? 0)) (bv_unsigned w mod 128 =? 115)
      | None => false end) in
    lazymatch u with true => idtac | false => fail end.
  Ltac w4to pc := do 40 (tryif w4at pc then idtac else
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif w4unimp p then fail else zstep
    | _ => w4if
    end).
  Definition W4HIDE (P : Prop) : Prop := P.
  Ltac w4err F0 M1 L1 L2 L3 ST := unfold W4HIDE in *; w4to AW4_EPI; release_frame F0 ST (SP + -376); release_frame M1 ST (SP + -224);
    release_frame L1 ST (SP + -184); release_frame L2 ST (SP + -144); release_frame L3 ST (SP + -104);
    eapply w4s_epi; eassumption.

  Ltac w4dc H := lazymatch type of H with _ /\ _ =>
    let A := fresh "cf" in let B := fresh "cf" in destruct H as [A B]; w4dc A; w4dc B | _ => idtac end.
  Ltac w4landb K := repeat (match type of K with context [Z.land ?x ?M] => w4lit M;
    let E := fresh "LB" in pose proof (w4s_landle x M ltac:(lia) ltac:(lia)) as E;
    let z := fresh "z" in set (z := Z.land x M) in *; clearbody z end).
  Ltac w4chk K CF := exfalso; clear - K CF; w4dc CF;
    unfold AIMG_HI in *; rewrite ?Z.shiftr_div_pow2 in K by lia; rewrite ?w4s_le16 in K by lia;
    rewrite ?w4s_landm in K by (Z.div_mod_to_equations; lia); rewrite ?w4s_land3 in K;
    rewrite ?zb_lxor_ones in K by lia; w4landb K; rewrite ?zb_lxor_ones in K by lia; Z.div_mod_to_equations; lia.
  Ltac w4x := repeat (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => w4if
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let b := eval vm_compute in (orb (p =? ABIT_INIT_F) (p =? AW4_S0C)) in lazymatch b with true => fail | false =>
          tryif w4unimp p then fail else zstep end
    end).
  Ltac w4chkall K := exfalso; unfold W4HIDE in *;
    repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
                         | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
                         | H : rng _ _ _ |- _ => clear H | H : ov_read_bytes _ _ _ _ = _ |- _ => clear H
                         | H : context [sval _] |- _ => tryif constr_eq H K then fail else clear H end;
    unfold AIMG_HI in *; rewrite ?Z.shiftr_div_pow2 in K by lia;
    rewrite ?w4s_landm in K by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia.
  Definition W4CK (b : byte) (a : Z) : Prop := sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b).
  Ltac w4chks K := lazymatch type of K with context [sval ?b] =>
    match goal with C : W4CK b _, B : Z.land (sval b) _ <> 0 |- _ =>
      exfalso; unfold W4CK in C; destruct C as [C|C];
      [ rewrite C in B; apply B; reflexivity | rewrite ?land7_mod in K; clear - K C; lia ]
    end end.
  Ltac w4lts K := lazymatch type of K with context [bv_lts _ _] => idtac end;
    unfold bv_lts in K; rewrite ?land7_mod in K;
    rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia); zify_bool K.
  Ltac w4rv R r := let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end).
  Ltac w4toJ J CF := do 30 (tryif w4at J then idtac else first [
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        first [w4if | (let K := fresh "KK" in rewrite ?sxb_sval; if_cases K; first [w4lts K | zify_cond K];
                       [ try (first [w4chks K | w4chk K CF]) | try (first [w4chks K | w4chk K CF]) ])]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif w4unimp p then fail else zstep
    end | idtac ]).
  Ltac w4tmp J := let o := eval vm_compute in (J - 556804) in
    lazymatch o with 7228 => constr:(12) | 7272 => constr:(14) | 7296 => constr:(14) | 7344 => constr:(17)
                | 7368 => constr:(17) end.
  Ltac w4sj t CF := rewrite ?sxb_sval;
    lazymatch goal with |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then Z_to_bv 64 ?J else _) ?fc ?rv ?m ?rom) =>
      let KJ := fresh "KJ" in let w := fresh "jw" in
      assert (KJ : forall w : word, evtF segs RNG Q (MS (@bvmap_set 5 word (Z_to_bv 5 t) w R) F (Z_to_bv 64 J) fc rv m rom));
      [ intros w; simp_regs
      | let K := fresh "KK" in if_cases K; zify_cond K;
        [ let v := w4rv R t in let H := fresh "KJv" in pose proof (KJ v) as H; revert H; simp_regs;
          exact (fun H => H)
        | w4toJ J CF; w4at J;
          let v := reg_val t in let H := fresh "KJv" in pose proof (KJ v) as H; revert H; simp_regs;
          exact (fun H => H) ] ]
    end.
  Ltac w4pco := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => eval vm_compute in (p - 556804) end.
  Ltac w4inC := let o := w4pco in lazymatch o with 7088 => idtac | 7100 => idtac | 7124 => idtac | 7156 => idtac end.
  Ltac w4inE := let o := w4pco in lazymatch o with 7072 => idtac | 7084 => idtac | 7596 => idtac | 7616 => idtac end.
  Ltac w4auto CF F0 M1 L1 L2 L3 ST := w4x; lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if bv_eqb (sxb _) _ then Z_to_bv 64 ?J else _) _ _ _ _) => let t := w4tmp J in w4sj t CF; w4auto CF F0 M1 L1 L2 L3 ST
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let K := fresh "KK" in rewrite ?sxb_sval; rewrite ?w4s_le16 by apply w4s_byte;
        if_cases K; first [w4lts K | zify_cond K];
        [ try (first [(w4chks K) | (w4chk K CF) | (w4inC; w4chkall K)])
        | try (first [(w4chks K) | (w4chk K CF) | (w4inC; w4chkall K)]) ];
        let H := fresh "brx" in rename K into H; try solve [w4inE; w4err F0 M1 L1 L2 L3 ST];
        w4auto CF F0 M1 L1 L2 L3 ST
    | _ => idtac
    end.

  Ltac w4arith := unfold W4HIDE in *;
    repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
                         | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
                         | H : rng _ _ _ |- _ => clear H | H : ov_read_bytes _ _ _ _ = _ |- _ => clear H
                         | H : context [sval _] |- _ => clear H end;
    pose proof (w4s_byte 0); pose proof (w4s_byte 1); pose proof (w4s_byte 2); pose proof (w4s_byte 3);
    pose proof (w4s_byte 4); pose proof (w4s_byte 5);
    unfold AIMG_HI in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia.
  Ltac w4ldr HR TLB := lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply (evtF_step_acc segs RNG);
        [ reflexivity
        | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          (exec_pre i); (exec_cbv; simp_is_x0; simp_regs; vnorm_for i); (rewrite HR); (rewrite ?zext_extract_le2; rewrite zx16_short by (clear - TLB; lia);
                         rewrite Z.mod_small by (clear - TLB; lia)); load_post; reflexivity
        | (solve_accs)
        | (simp_regs; vnorm_for i; mem_after_store_opt; post_step i) ]
      end
    end
  end.

  Lemma w4s0_slow : w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.
  Proof using All.
    intros fr mid l256 l296 l336 mm x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 HW.
    unfold W4F in HW.
    destruct HW as ((buf & OB & OBL) & SRC & CBS & DTH & ST & F0 & F0S & M1 & M1S & L1 & L1S & L2 & L2S & L3 & L3S & FRA & MI & MU & WM).
    pose proof w4s_sp as SPB. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC.
    pose proof RTC as RTC0. unfold artcells in RTC0.
    destruct RTC0 as (_ & GOT & _ & _ & SHB & _).
    pose proof w4s_blocks as (B1 & B2 & B3 & B4 & B5 & B6). pose proof w4s_d0 as (D1 & D2 & D3).
    pose proof (conj SPB (conj B1 (conj B2 (conj B4 (conj B5 (conj D1 (conj D2 DC))))))) as CF.
    replace (SP + -480 + 104) with (SP + -376) in M1 by lia. replace (SP + -480 + 256) with (SP + -224) in L1 by lia.
    replace (SP + -480 + 296) with (SP + -184) in L2 by lia. replace (SP + -480 + 336) with (SP + -144) in L3 by lia.
    apply rw_cells_forget in F0. destruct F0 as (j0 & F0). rewrite F0S in F0.
    apply rw_cells_forget in M1. destruct M1 as (jm & M1). rewrite M1S in M1.
    apply rw_cells_forget in L1. destruct L1 as (j256 & L1). rewrite L1S in L1.
    apply rw_cells_forget in L2. destruct L2 as (j296 & L2). rewrite L2S in L2.
    apply rw_cells_forget in L3. destruct L3 as (j336 & L3). rewrite L3S in L3.
    pose proof (w4s_unp mm MU) as (UDT & USS).
    pose proof (hb_unpoisoned AI L RNG st LB m0 pdt DT DTL AH HDT) as (UDT0 & DT16 & _ & K2D & _ & RDT & RDS & _).
    assert (DTL8 : 8 <= DTL) by (cbv [DTABLE_BYTES HufHarness.DT_BYTES]; pose proof (Z.pow_le_mono_r 2 1 mtl ltac:(lia) ltac:(lia)); lia).
    assert (RSTK : rng RNG (SP + -480) 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    unfold AW4_SLOW.
    destruct (Z_lt_le_dec 0 n) as [NP | NZ].
    2: { w4auto CF F0 M1 L1 L2 L3 ST. }
    pose proof (USS NP) as USS'. destruct (SRCB NP) as (p & HB & SB1 & SB2).
    pose proof (hb_unpoisoned AI L RNG st LB m0 p SBL (SBH - SBL) AH HB) as (USB0 & A16 & _ & K2 & STOP & RS1 & RS2 & _).
    unfold ablk, AIMG_HI, KLS in K2. pose proof (@ATOP_lo rc) as HA. pose proof (@ATOP_hi rc) as HA2.
    assert (RSS : rng RNG SS n) by (eapply rng_sub; [exact RS1 | lia | lia]).
    pose proof (conj STOP (conj DT16 (conj S16 (conj SB1 (conj SB2 (conj NP (conj K2 (conj HA (conj HA2 CF))))))))) as CF2.
    assert (RSB : rng RNG (SS / 8 + AW4_KSB) 1).
    { assert (Q : SBL / 8 <= SS / 8 /\ SS / 8 + 1 <= SBL / 8 + shlen (SBH - SBL + 7))
        by (rewrite shlenE; clear - A16 SB1 SB2 NP; Z.div_mod_to_equations; lia).
      replace (SS / 8 + AW4_KSB) with (shad SBL + (SS / 8 - SBL / 8)) by (rewrite shad_div; unfold ASHOFF, AW4_KSB; lia).
      eapply rng_sub; [exact RS2 | lia | lia]. }
    w4auto CF2 F0 M1 L1 L2 L3 ST.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      assert (USB : unpoisoned m SBL (SBL + (SBH - SBL)))
        by (eapply unpoisoned_munch; [exact USB0 | eassumption |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; lia);
      assert (SBS : rw_cells bsegs m (SS / 8 + AW4_KSB) [C1 (Z_to_bv 8 0)])
    end.
    { replace (SS / 8 + AW4_KSB) with (ASHOFF + SS / 8) by (unfold ASHOFF, AW4_KSB; lia).
      apply (rw_cells_C1_of_byte bsegs); [unfold ASHOFF; Z.div_mod_to_equations; lia | unfold ASHOFF; Z.div_mod_to_equations; lia |].
      eapply unpoisoned_full; [exact USB | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]. }
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      destruct (AF_fse_rd_base.chkB m SBL (SBL + (SBH - SBL)) (SS + 1) USB ltac:(lia) ltac:(lia)) as (b1 & RB1 & CK1 & SR1);
      change (W4CK b1 (SS + 1)) in CK1;
      destruct (AF_fse_rd_base.chkB m SBL (SBL + (SBH - SBL)) (SS + 2) USB ltac:(lia) ltac:(lia)) as (b2 & RB2 & CK2 & SR2);
      change (W4CK b2 (SS + 2)) in CK2;
      destruct (AF_fse_rd_base.chkB m SBL (SBL + (SBH - SBL)) (SS + 3) USB ltac:(lia) ltac:(lia)) as (b3 & RB3 & CK3 & SR3);
      change (W4CK b3 (SS + 3)) in CK3;
      destruct (AF_fse_rd_base.chkB m SBL (SBL + (SBH - SBL)) (SS + 4) USB ltac:(lia) ltac:(lia)) as (b4 & RB4 & CK4 & SR4);
      change (W4CK b4 (SS + 4)) in CK4;
      destruct (AF_fse_rd_base.chkB m SBL (SBL + (SBH - SBL)) (SS + 5) USB ltac:(lia) ltac:(lia)) as (b5 & RB5 & CK5 & SR5);
      change (W4CK b5 (SS + 5)) in CK5
    end.
    pose proof (w4s_rsb RNG SBL SBH (SS + 1) RS2 A16 ltac:(lia)) as RG1.
    pose proof (w4s_rsb RNG SBL SBH (SS + 2) RS2 A16 ltac:(lia)) as RG2.
    pose proof (w4s_rsb RNG SBL SBH (SS + 3) RS2 A16 ltac:(lia)) as RG3.
    pose proof (w4s_rsb RNG SBL SBH (SS + 4) RS2 A16 ltac:(lia)) as RG4.
    pose proof (w4s_rsb RNG SBL SBH (SS + 5) RS2 A16 ltac:(lia)) as RG5.
    pose proof (w4s_rd0 _ _ _ SRC ltac:(lia)) as RD0.
    pose proof (w4s_rd1 _ _ _ 1 SRC ltac:(lia)) as RD1.
    pose proof (w4s_rd1 _ _ _ 2 SRC ltac:(lia)) as RD2.
    pose proof (w4s_rd1 _ _ _ 3 SRC ltac:(lia)) as RD3.
    pose proof (w4s_rd1 _ _ _ 4 SRC ltac:(lia)) as RD4.
    pose proof (w4s_rd1 _ _ _ 5 SRC ltac:(lia)) as RD5.
    pose proof (conj (w4s_byte 0) (conj (w4s_byte 1) (conj (w4s_byte 2) (conj (w4s_byte 3) (conj (w4s_byte 4)
      (conj (w4s_byte 5) (conj DTL8 CF2))))))) as CF3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      assert (UDTm : unpoisoned m DT (DT + DTL))
        by (eapply unpoisoned_munch; [exact UDT0 | eassumption |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
            unfold ablk, AIMG_HI, KLS in K2D; lia);
      assert (SDT : rw_cells bsegs m (Z.shiftr (Z.land DT 18446744073709551615) 3 + AW4_KSB) [C1 (Z_to_bv 8 0)])
    end.
    { assert (DTB : 0 <= DT < 2^47) by (clear - B1 B2 HA2 DTL8; unfold AIMG_HI in *; lia).
      rewrite w4s_landm by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      change (DT / 8 + AW4_KSB) with (DT / 8 + AW4_KSB).
      replace (DT / 8 + AW4_KSB) with (ASHOFF + DT / 8) by (unfold ASHOFF, AW4_KSB; lia).
      apply (rw_cells_C1_of_byte bsegs); [unfold ASHOFF; Z.div_mod_to_equations; lia | unfold ASHOFF; Z.div_mod_to_equations; lia |].
      eapply unpoisoned_full; [exact UDTm | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]. }
    assert (RGD : rng RNG (Z.shiftr (Z.land DT 18446744073709551615) 3 + AW4_KSB) 1).
    { apply (w4s_rsb RNG DT (DT + DTL)); [replace (DT + DTL - DT + 7) with (DTL + 7) by lia; exact RDS | exact DT16 |].
      assert (DTB : 0 <= DT < 2^47) by (clear - B1 B2 HA2 DTL8; unfold AIMG_HI in *; lia).
      rewrite w4s_landm by lia. lia. }
    rewrite ?(Z.shiftr_div_pow2 SS 3) by lia; change (2^3) with 8.
    set (gS := SS / 8) in *. unfold AW4_KSB in *.
    change (W4HIDE (DT + DTL <= SS \/ SS + n <= DT)) in DJ1. change (W4HIDE (DST + dcap <= SS \/ SS + n <= DST)) in DJ2.
    change (W4HIDE (DT + DTL <= DST \/ DST + dcap <= DT)) in DJ3.
    match type of K2 with ?T => change (W4HIDE T) in K2 end.
    match type of DSTF with ?T => change (W4HIDE T) in DSTF end.
    w4auto CF3 F0 M1 L1 L2 L3 ST.
    all: try (w4at 564364; match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
        assert (UDT2 : unpoisoned m DT (DT + DTL))
          by (eapply unpoisoned_munch; [exact UDT0 | eassumption |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
              unfold ablk, AIMG_HI, KLS in K2D; lia);
        assert (SDT2 : rw_cells bsegs m (Z.shiftr (Z.land DT 18446744073709551615) 3 + AW4_KSB) [C1 (Z_to_bv 8 0)])
      end;
      [ assert (DTB : 0 <= DT < 2^47) by (clear - B1 B2 HA2 DTL8; unfold AIMG_HI in *; lia);
        rewrite w4s_landm by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        replace (DT / 8 + AW4_KSB) with (ASHOFF + DT / 8) by (unfold ASHOFF, AW4_KSB; lia);
        apply (rw_cells_C1_of_byte bsegs); [unfold ASHOFF; Z.div_mod_to_equations; lia | unfold ASHOFF; Z.div_mod_to_equations; lia |];
        eapply unpoisoned_full; [exact UDT2 | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]
      | unfold AW4_KSB in SDT2; w4auto CF3 F0 M1 L1 L2 L3 ST ]).
    all: try (w4at 564428; match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
        assert (TLB : 1 <= tl <= 12 /\ 1 <= mtl <= 12)
          by (destruct TOK as (TOK1 & _); unfold HUF_TABLELOG_MAX in TOK1; lia);
        assert (RDT2 : ov_read_bytes bsegs m (Z_to_bv 64 (DT + 2)) 2 = Some (le2 (Z_to_bv 64 (tl + 256 * mtl))))
          by (rewrite le2_two_bytes by lia;
              change (Z_to_bv 64 (DT + 2)) with (wa (DT + 2)); rewrite (bytes_at_read bsegs m DT _ 2 2 DTH) by (cbn; lia);
              reflexivity)
      end; w4ldr RDT2 TLB; w4auto CF3 F0 M1 L1 L2 L3 ST).
    all: try (w4at AW4_S0C; rewrite ?Z.shiftr_div_pow2 in F0 by lia; rewrite ?Z.shiftr_div_pow2 by lia; try change (2^2) with 4 in F0; try change (2^2) with 4;
      try replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 3 * ((dcap + 3) / 4)) by ring;
      try replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 2 * ((dcap + 3) / 4)) in F0 by ring;
      try replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 2 * ((dcap + 3) / 4)) by ring;
      try replace (Znth 0 src + 256 * Znth 1 src + (Znth 2 src + 256 * Znth 3 src) + (Znth 4 src + 256 * Znth 5 src) + 6)
        with (6 + (Znth 0 src + 256 * Znth 1 src) + (Znth 2 src + 256 * Znth 3 src) + (Znth 4 src + 256 * Znth 5 src)) by ring;
      apply (rw_cells_split_CB bsegs _ _ [] 32 _ _ [8;8;8;8]%nat) in F0; [| reflexivity]; cbn [mk_CB_cells app] in F0;
      apply (rw_cells_split_CB bsegs _ _ [_;_;_;_;_] 24 _ _ [8;8;8]%nat) in F0; [| reflexivity]; cbn [mk_CB_cells app] in F0;
      w4c8 F0; apply (rw_cells_split_CB bsegs _ _ [] 152 _ [] [40;112]%nat) in M1; [| reflexivity]; cbn [mk_CB_cells app] in M1;
      replace (SP + -376) with (SP + -480 + 104) in M1 by lia; replace (SP + -224) with (SP + -480 + 256) in L1 by lia;
      replace (SP + -184) with (SP + -480 + 296) in L2 by lia; replace (SP + -144) with (SP + -480 + 336) in L3 by lia;
      pose proof W4S0C as WC; unfold w4s0c_goal in WC;
      eapply WC; [ unfold W4F;
        first [ refine (conj (ex_intro _ buf (conj OB OBL)) (conj SRC (conj CBS (conj DTH (conj ST (conj F0 (conj _ (conj M1 (conj _ (conj L1 (conj _
                  (conj L2 (conj _ (conj L3 (conj _ (conj FRA (conj MI (conj MU WM)))))))))))))))))); reflexivity ]
      | .. ];
      first [ lia
            | (pose proof (w4s_byte 0); pose proof (w4s_byte 1); pose proof (w4s_byte 2); pose proof (w4s_byte 3);
               pose proof (w4s_byte 4); pose proof (w4s_byte 5); lia)
            | w4arith ]).
  Qed.
End W4S0.
End CANSEC1.

