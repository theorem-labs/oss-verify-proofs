(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow IcptSpec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2 L_harnw1 L_harnw2 L_harnw3 L_harnw4 L_harnw5 L_harn1 L_harn2 L_harn3.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow IcptSpec2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw3.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw4.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw5.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn3.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma hz_frame_split : forall (m : mem) a z0 j8 (r : list cell), rw_cells bsegs m a (C8 z0 :: CB 24 j8 :: r) ->
  exists ja jb jc, rw_cells bsegs m a [C8 z0] /\ rw_cells bsegs m (a + 8) [CB 8 ja] /\ rw_cells bsegs m (a + 16) [CB 8 jb] /\ rw_cells bsegs m (a + 24) [CB 8 jc]
                   /\ rw_cells bsegs m (a + 32) r.
Proof.
  intros m a z0 j8 r H.
  apply (rw_cells_split_CB bsegs m a [C8 z0] 24 j8 r [8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  exists (firstn 8 j8), (firstn 8 (skipn 8 j8)), (firstn 8 (skipn 8 (skipn 8 j8))).
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H.
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H. replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H by lia.
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H. replace (a + 16 + Z.of_nat 8) with (a + 24) in H by lia.
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H. replace (a + 24 + Z.of_nat 8) with (a + 32) in H by lia. exact H.
Qed.

Lemma hz_frame_join : forall (m : mem) a z0 X1 X2 X3 (r : list cell), csize X1 = 8%nat -> csize X2 = 8%nat -> csize X3 = 8%nat ->
  rw_cells bsegs m a [C8 z0] -> rw_cells bsegs m (a + 8) [X1] -> rw_cells bsegs m (a + 16) [X2] -> rw_cells bsegs m (a + 24) [X3] -> rw_cells bsegs m (a + 32) r ->
  exists j8, rw_cells bsegs m a (C8 z0 :: CB 24 j8 :: r).
Proof.
  intros m a z0 X1 X2 X3 r S1 S2 S3 H0 H1 H2 H3 HR. exists (cells_bytes [X1; X2; X3]).
  assert (HJ : rw_cells bsegs m a ([C8 z0] ++ [X1] ++ [X2] ++ [X3] ++ r)).
  { apply rw_cells_app. split; [exact H0|]. cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [exact H1|]. cbn [cells_size Nat.add]. rewrite S1.
    apply rw_cells_app. split; [replace (a + Z.of_nat 8 + Z.of_nat (8 + 0)) with (a + 16) by lia; exact H2|]. cbn [cells_size Nat.add]. rewrite S2.
    apply rw_cells_app. split; [replace (a + Z.of_nat 8 + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) with (a + 24) by lia; exact H3|]. cbn [cells_size Nat.add]. rewrite S3.
    replace (a + Z.of_nat 8 + Z.of_nat (8 + 0) + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) with (a + 32) by lia. exact HR. }
  apply (rw_cells_recast' m a _ _ HJ).
  - pose proof (proj1 (proj1 H1)) as (W1 & _). pose proof (proj1 (proj1 H2)) as (W2 & _). pose proof (proj1 (proj1 H3)) as (W3 & _). pose proof (proj1 (proj1 HR)) as WR.
    split; [exact I|]. split; [| exact WR]. cbn [cell_wf]. rewrite (cells_bytes_length [X1; X2; X3]) by (cbn [cells_wf]; tauto).
    cbn [cells_size]. rewrite S1, S2, S3. reflexivity.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

Section Front.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis MAL : malloc_contract RT.
Hypothesis MAL0 : malloc0_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis MCMP : memcmp_icontract RT.
Hypothesis B2BC : b2bc_cps RT LIB enc_ok.
Hypothesis B2BD : b2bd_cps RT LIB dec_ok.
Hypothesis RTW : round_trip_weak enc_ok dec_ok.

Variables (Σ0 : rts RT) (PMc : Model -> Prop) (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m0 : mem) (d : Z) (bs : list byte)
          (p0 n0 spa Fr : Z).
Local Notation n := (Z.of_nat (length bs)).
Local Notation live0 := (rt_live RT Σ0).
Local Notation OKT := (hz_ok RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr).
Local Notation HMc := (HM RT Σ0 cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 spa Fr).
Local Notation HSc := (HS RT Σ0 Fr).
Local Notation HQc := (HQ RT LIB Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0).
Hypothesis OK : OKT.

Local Ltac ul := unfold B2B_STACK, B2B_LIVE, B2BD_COST, B2BC_COST, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt bsegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

Local Notation r33 f := (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* [comment removed for export] *)
Lemma harn_cost : forall k, 0 <= k < 2^26 -> 1 + mcost (nZ_of k) + B2BC_COST + mcost (2 * k) + B2BD_COST <= FUZZ_COST.
Proof.
  intros k Hk. unfold mcost, nZ_of, B2BC_COST, B2BD_COST, FUZZ_COST.
  assert (k / 100 <= k) by (apply Z.div_le_upper_bound; lia).
  destruct (k + 600 + k / 100 <=? 64512); destruct (2 * k <=? 64512); lia.
Qed.

Lemma mcost_nonneg : forall k, 0 <= k -> 0 <= mcost k.
Proof. intros k Hk. unfold mcost. destruct (k <=? 64512); lia. Qed.

(* [comment removed for export] *)
Lemma hz_mid_cps : forall (Σ : rts RT) (m : mem) zb rc dlv (j6 : list byte) (s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(zb, nZ_of n)] ->
  rw_cells bsegs m (Fr + 32) [C4 (Z_to_bv 64 dlv)] -> rw_cells bsegs m (Fr + 48) [CB 8 j6] ->
  ((rc = 0 /\ exists str, enc_ok bs (bs_of n) (wf_of n) str /\ dlv = Z.of_nat (length str) /\ dlv <= nZ_of n /\ bytes_at bsegs m zb str) \/ (-9 <= rc < 0)) ->
  rt_credit RT Σ0 - FUZZ_COST + mcost (2 * n) + B2BD_COST <= rt_credit RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 RA_B2BC)) fc None m (seg_rom bsegs)))) HQc.
Proof using OK AF LIB_loc MAL MAL0 FRE MCMP B2BD RTW.
  intros Σ m zb rc dlv j6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S NZC NOJ RES CRX T c Hc Hk.
  pose proof H as (ART0 & MI0 & ST0 & _). pose proof S as (LV & FRS & SP0).
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FLO OK) as FLO. pose proof (hz_NB OK) as NB. pose proof (nZ_bound n ltac:(lia)) as NZB. pose proof (hz_CRB OK) as CRB.
  pose proof (mcost_nonneg (2 * n) ltac:(lia)) as MC0.
  assert (INZ : In (zb, nZ_of n) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m zb (nZ_of n) ART0 INZ) as (ZB0 & ZBH & _). rewrite SP0 in ZBH. pose proof (hz_LOW OK) as LOW. pose proof (hz_SP0R OK) as SP0R.
  destruct RES as [(-> & str & ENC & -> & DLB & ZBB)|RCN].
  - (* [comment removed for export] *)
    pose proof (hz_wD usp spa Fr d n zb j6 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 c11 t3 t4 t5 t6 F fc m ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ul) NOJ MI0) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & j7 & -> & MU1 & WM1 & MI1 & NOC1) & Hc1'). clear Hc1.
    assert (ART1 : ART RT Σ m1).
    { apply (hs_art_munch AF OK Σ _ _ m m1 ART0 S MU1 WM1). intros x H1 H2 H3. cbn [outside]. lia. }
    assert (HM1 : HMc Σ m1).
    { apply (hm_step OK Σ Σ m m1 H ART1 MI1 (stk_wmono' _ _ _ _ ST0 WM1)). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside].
      pose proof (core_not_cells OK x Hx). lia. }
    assert (NZC1 : rw_cells bsegs m1 (Fr + 32) [C4 (Z_to_bv 64 (Z.of_nat (length str)))]).
    { apply (rw_cells_agree_nw bsegs m m1 _ _ NZC). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. lia. }
    assert (ZBB1 : bytes_at bsegs m1 zb str).
    { apply (bytes_at_agree bsegs m m1 _ _ ZBB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside].
      pose proof (hs_chunk_frame AF ART0 S (or_introl eq_refl)) as CF. lia. }
    refine (cps_realizes bsegs _ _ T cf1 (hz_malloc_step RT LIB AF MAL MAL0 Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK
                                            Σ m1 [(zb, nZ_of n)] (2 * n) 0x814c8 (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7
                                            (Z_to_bv 64 (Fr + 48)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc HM1 S ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia) ltac:(ul)) Hc1' _).
    intros cf2 (Σ1 & ob & Hc2 & S1 & CR1 & OB0 & OBT).
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & HM2 & PR2 & OBW) & Hc2').
    clear Hc2. rewrite LV in PR2.
    assert (AGF : forall a k, Fr <= a -> a + k <= Fr + 56 -> agree_on (fun x => a <= x < a + k) m1 m2).
    { intros a k A1 A2. apply (agree_of_pres _ _ _ _ _ _ PR2). intros x Hx. right; right; right; left. exists Fr, 0%nat. split; [left; reflexivity|].
      change (fs_size 0) with 64. lia. }
    exact (hz_dec_cps RT LIB enc_ok dec_ok AF LIB_loc FRE MCMP B2BD RTW Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK
             Σ1 m2 zb ob (Z.max (2 * n) 1) str j7 s7 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F1 fc1 HM2 S1 eq_refl OBW ENC DLB
             ltac:(apply (bytes_at_agree bsegs m1 m2 _ _ ZBB1); apply (agree_of_pres _ _ _ _ _ _ PR2); intros x Hx; right; right; left; exists zb, (nZ_of n);
                   split; [left; reflexivity| lia])
             ltac:(apply (rw_cells_agree_nw bsegs m1 m2 _ _ NZC1); apply AGF; cbn [cells_size csize Nat.add]; lia)
             ltac:(apply (rw_cells_agree_nw bsegs m1 m2 _ _ NOC1); apply AGF; cbn [cells_size csize Nat.add]; lia)
             ltac:(ul) T cf2 Hc2' Hk).
  - (* [comment removed for export] *)
    pose proof (hz_wD_err usp spa Fr d n zb rc gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 c11 t3 t4 t5 t6 F fc m RCN ltac:(ul)) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1. destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & -> & Hc1'). clear Hc1.
    exact (hz_tail_cps RT LIB AF LIB_loc FRE Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK Σ m zb (nZ_of n)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc H S ltac:(lia) ltac:(ul) T cf1 Hc1' Hk).
Qed.

(* [comment removed for export] *)
Lemma hz_front_cps : forall (Σ1 : rts RT) (m : mem) (z0 : word) (j8 : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  ART RT Σ1 m -> mem_inv bsegs m -> stk bsegs m lo spa -> agree_on (ACL RT Σ0 usp) m0 m ->
  rw_cells bsegs m (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  (spa = usp + -128 \/ (spa = usp + -144 /\ exists jg : list byte, rw_cells bsegs m (usp + -144) [CB 16 jg])) ->
  HSc Σ1 [] -> wr_at bsegs m Fr 56 -> wr_at bsegs m (shad Fr) 8 -> rt_credit RT Σ1 = rt_credit RT Σ0 - 1 ->
  cps bsegs (ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x81374) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 Fr) a1 a2 a3 a4 a5 a6 a7
             c2 (Z_to_bv 64 n) (Z_to_bv 64 d) c5 c6 c7 c8 (Z_to_bv 64 SHB) c10 c11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 0x81374)) fc None m (seg_rom bsegs)))) HQc.
Proof using OK AF LIB_loc MAL MAL0 FRE MCMP B2BC B2BD RTW.
  intros Σ1 m z0 j8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc ART1 MI1 ST1 PR1 FR1 GAP1 S1 WF WS CR1 T c Hc Hk.
  pose proof S1 as (LV1 & FRS1 & SP1). cbn [app] in LV1.
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST. pose proof (hz_F64 OK) as F64. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FPL OK) as FPL. pose proof (hz_FLO OK) as FLO. pose proof (hz_NB OK) as NB. pose proof (nZ_bound n ltac:(lia)) as NZB. pose proof (hz_CRB OK) as CRB.
  pose proof (hz_D0 OK) as D0. pose proof (hz_DHI OK) as DHI. pose proof (hz_SP0R OK) as SP0R. pose proof (hz_LOW OK) as LOW. pose proof (shad_F_lo OK) as SHLO.
  pose proof (harn_cost n ltac:(lia)) as COST. pose proof (mcost_nonneg (nZ_of n) ltac:(lia)) as MCZ. pose proof (mcost_nonneg (2 * n) ltac:(lia)) as MCO.
  destruct (wr_at_rw_CB m Fr 56 WF ltac:(lia)) as (jh & HDRJ). destruct (wr_at_rw_CB m (shad Fr) 8 WS ltac:(lia)) as (js & SHJ).
  (* [comment removed for export] *)
  unfold hz_frame in FR1. destruct (hz_frame_split m (usp + -128) z0 j8 _ FR1) as (ja & jb & jc & FA & FB1 & FB2 & FB3 & FRR).
  replace (usp + -128 + 8) with (usp + -120) in FB1 by lia. replace (usp + -128 + 16) with (usp + -112) in FB2 by lia.
  replace (usp + -128 + 24) with (usp + -104) in FB3 by lia. replace (usp + -128 + 32) with (usp + -96) in FRR by lia.
  assert (SLOT : exists jsl, rw_cells bsegs m (spa + 24) [CB 8 jsl]).
  { destruct (hz_SPA1 OK) as [E|E]; rewrite E; [exists jc; replace (usp + -128 + 24) with (usp + -104) by lia; exact FB3|
                                                  exists ja; replace (usp + -144 + 24) with (usp + -120) by lia; exact FB1]. }
  destruct SLOT as (jsl & SLOT).
  pose proof (hz_wB usp spa Fr d n jh js jsl gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 c2 c5 c6 c7 c8 c10 c11 t3 t4 t5 t6 F fc m ltac:(lia) F64 FPL ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(ul) ltac:(lia) HDRJ SHJ SLOT MI1) as W.
  to_cps W c Hc Σ1 MST. intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m2 & h0 & h1 & h2 & b1 & b2 & b3 & b4 & b5 & j3 & j5 & j6 & -> & MU2 & WM2 & MI2 & FC2 & SH2 & SL2) & Hc1').
  clear Hc1.
  assert (ART2 : ART RT Σ1 m2).
  { apply (hs_art_munch AF OK Σ1 _ _ m m2 ART1 S1 MU2 WM2). intros x H1 H2 H3. cbn [outside]. lia. }
  assert (AGS : forall a k, spa <= a -> a + k <= usp -> (a + k <= spa + 24 \/ spa + 32 <= a) -> agree_on (fun x => a <= x < a + k) m m2).
  { intros a k A1 A2 A3. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [outside]. lia. }
  (* [comment removed for export] *)
  assert (FR2 : exists j8', rw_cells bsegs m2 (usp + -128) (hz_frame (C8 z0) j8' c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)).
  { unfold hz_frame.
    assert (FA2 : rw_cells bsegs m2 (usp + -128) [C8 z0]) by (apply (rw_cells_agree_nw bsegs m m2 _ _ FA); apply AGS; cbn [cells_size csize Nat.add]; lia).
    assert (FB22 : rw_cells bsegs m2 (usp + -112) [CB 8 jb]) by (apply (rw_cells_agree_nw bsegs m m2 _ _ FB2); apply AGS; cbn [cells_size csize Nat.add]; lia).
    assert (FRR2 : rw_cells bsegs m2 (usp + -96) [C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra])
      by (apply (rw_cells_agree_nw bsegs m m2 _ _ FRR); apply AGS; cbn [cells_size csize Nat.add]; lia).
    destruct (hz_SPA1 OK) as [E|E].
    - assert (FB12 : rw_cells bsegs m2 (usp + -120) [CB 8 ja]) by (apply (rw_cells_agree_nw bsegs m m2 _ _ FB1); apply AGS; cbn [cells_size csize Nat.add]; lia).
      rewrite E in SL2. replace (usp + -128 + 24) with (usp + -104) in SL2 by lia.
      apply (hz_frame_join m2 (usp + -128) z0 (CB 8 ja) (CB 8 jb) (C8 (Z_to_bv 64 Fr))); try reflexivity; try assumption.
      + replace (usp + -128 + 8) with (usp + -120) by lia. exact FB12.
      + replace (usp + -128 + 16) with (usp + -112) by lia. exact FB22.
      + replace (usp + -128 + 24) with (usp + -104) by lia. exact SL2.
      + replace (usp + -128 + 32) with (usp + -96) by lia. exact FRR2.
    - assert (FB32 : rw_cells bsegs m2 (usp + -104) [CB 8 jc]) by (apply (rw_cells_agree_nw bsegs m m2 _ _ FB3); apply AGS; cbn [cells_size csize Nat.add]; lia).
      rewrite E in SL2. replace (usp + -144 + 24) with (usp + -120) in SL2 by lia.
      apply (hz_frame_join m2 (usp + -128) z0 (C8 (Z_to_bv 64 Fr)) (CB 8 jb) (CB 8 jc)); try reflexivity; try assumption.
      + replace (usp + -128 + 8) with (usp + -120) by lia. exact SL2.
      + replace (usp + -128 + 16) with (usp + -112) by lia. exact FB22.
      + replace (usp + -128 + 24) with (usp + -104) by lia. exact FB32.
      + replace (usp + -128 + 32) with (usp + -96) by lia. exact FRR2. }
  destruct FR2 as (j8' & FR2).
  (* [comment removed for export] *)
  change [C8 h0; C8 h1; C8 h2; CB 8 j3; C4 (Z_to_bv 64 (nZ_of n)); CB 12 j5; CB 8 j6]
    with ([C8 h0] ++ [C8 h1; C8 h2; CB 8 j3] ++ [C4 (Z_to_bv 64 (nZ_of n))] ++ [CB 12 j5] ++ [CB 8 j6]) in FC2.
  apply rw_cells_app in FC2 as (HDR2 & FC2). apply rw_cells_app in FC2 as (_ & FC2). apply rw_cells_app in FC2 as (NZC2 & FC2).
  apply rw_cells_app in FC2 as (_ & NOJ2). cbn [cells_size csize Nat.add] in NZC2, NOJ2.
  replace (Fr + Z.of_nat 8 + Z.of_nat 24) with (Fr + 32) in NZC2 by lia. replace (Fr + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 4 + Z.of_nat 12) with (Fr + 48) in NOJ2 by lia.
  assert (HM2 : HMc Σ1 m2).
  { split; [exact ART2|]. split; [exact MI2|]. split; [exact (stk_wmono' _ _ _ _ ST1 WM2)|].
    split; [apply (agree_trans _ m0 m m2 PR1); apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [outside];
            destruct (hz_FAP OK x Hx) as (A1 & A2); rewrite (shad_F64 OK) in A2;
            assert (~ (spa + 24 <= x < spa + 32)) by (intros Hs; destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]];
              [lia| pose proof (client_static_range x Hx); ul| destruct Hx as (q & k & Hq & Hk'); pose proof (af_live_range RT AF Σ1 m q k ART1 ltac:(rewrite LV1; exact Hq)) as (_ & R & _);
                rewrite SP1 in R; lia| destruct Hx as (f & k & [] & _)| destruct Hx as (f & k & [] & _)]); lia|].
    split; [exists z0, j8'; exact FR2|].
    split; [destruct GAP1 as [E|(E & jg & GP)]; [left; exact E| right; split; [exact E|]; exists jg; apply (rw_cells_agree_nw bsegs m m2 _ _ GP); apply AGS;
            cbn [cells_size csize Nat.add]; lia]|].
    split; [exists h0; exact HDR2| exact SH2]. }
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T cf1 (hz_malloc_step RT LIB AF MAL MAL0 Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK
                                          Σ1 m2 [] (nZ_of n) 0x81434 (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) c6 c7 c8
                                          _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc HM2 S1 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia) ltac:(ul)) Hc1' _).
  intros cf2 (Σ2 & zb & Hc2 & S2 & CR2 & ZB0 & ZBT). replace (Z.max (nZ_of n) 1) with (nZ_of n) in * by lia.
  destruct (ASTA_unpack RT Σ2 _ _ cf2 Hc2) as (ms2 & (m3 & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & HM3 & PR3 & ZBW) & Hc2').
  clear Hc2. rewrite LV1 in PR3. pose proof HM3 as (ART3 & MI3 & ST3 & _ & _ & _ & _ & SH3). pose proof S2 as (LV2 & FRS2 & SP2). cbn [app] in LV2.
  assert (AGF : forall a k, Fr <= a -> a + k <= Fr + 56 -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k A1 A2. apply (agree_of_pres _ _ _ _ _ _ PR3). intros x Hx. right; right; right; left. exists Fr, 0%nat. split; [left; reflexivity|].
    change (fs_size 0) with 64. lia. }
  assert (NZC3 : rw_cells bsegs m3 (Fr + 32) [C4 (Z_to_bv 64 (nZ_of n))]) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ NZC2); apply AGF; cbn [cells_size csize Nat.add]; lia).
  assert (NOJ3 : rw_cells bsegs m3 (Fr + 48) [CB 8 j6]) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ NOJ2); apply AGF; cbn [cells_size csize Nat.add]; lia).
  (* [comment removed for export] *)
  pose proof (hz_wC usp spa Fr d n zb gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c6 c7 c8 c11 w3 w4 w5 w6 F1 fc1 m3 ltac:(lia) ltac:(ul) MI3) as W.
  to_cps W cf2 Hc2' Σ2 MST. intros cf3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ cf3 Hc3) as (ms3 & (a7' & ->) & Hc3'). clear Hc3.
  destruct (wr_at_rw_CB m3 zb (nZ_of n) ZBW ltac:(lia)) as (junk & ZBJ).
  destruct (hz_sh0_parts m3 (shad Fr) SH3) as (SH4 & _).
  assert (ESH : shad (Fr + 32) = shad Fr + 4) by (unfold shad; Z.div_mod_to_equations; lia).
  assert (INZ : In (zb, nZ_of n) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T cf3 _ Hc3' _).
  { eapply (r33 (B2BC Σ2 PMc) m3 zb (Fr + 32) d bs junk lo); try reflexivity.
    - exact (hz_FDO OK).
    - exact MST.
    - exact (hz_TP OK).
    - lia.
    - ul.
    - exact (hm_payload OK Σ2 m3 HM3).
    - destruct (hz_INP OK) as [E|(IN0 & P0 & P1)]; [right; exact E| left]. exists p0, n0. split; [rewrite LV2; right; exact IN0|]. split; [lia|]. split; [lia|].
      intros E. injection E as E1 E2. exact (hs_fresh AF OK Σ2 m3 _ zb (nZ_of n) ART3 S2 (or_introl eq_refl) ltac:(lia) (p0, n0) IN0 E1).
    - exact INZ.
    - exact ZBJ.
    - exists Fr, 0%nat. split; [rewrite FRS2; left; reflexivity|]. change (fs_size 0) with 64. lia.
    - exact NZC3.
    - Z.div_mod_to_equations. lia.
    - rewrite ESH. exact SH4.
    - intros p k Hin. rewrite LV2 in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; lia| pose proof (hz_POS OK p k Hin); lia].
    - rewrite LV2. cbn [length]. pose proof (hz_LVB OK). ul.
    - rewrite FRS2. cbn. unfold B2B_FRAMES, FRAMES_MAX. lia.
    - ul.
    - exact (hm_record OK Σ2 m3 HM3).
    - exact (hm_lib LIB_loc OK Σ2 m3 HM3).
    - exact ART3.
    - exact MI3.
    - rewrite (hz_EU OK). exact ST3.
    - rewrite SP2. exact LOW.
    - rewrite (hz_EU OK). pose proof (hz_LOR OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPT OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPA2 OK). Z.div_mod_to_equations. lia.
    - rewrite (hz_EU OK), SP2. pose proof (hz_SPS OK). lia. }
  intros cf4 (Σ3 & rc & dlv & Hc4 & LV3 & FRS3 & SP3 & CR3).
  destruct (ASTA_unpack RT Σ3 _ _ cf4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PR4 & DLC & _ & RES) & Hc4'). clear Hc4.
  destruct RS4 as (x0 & x1 & x2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & x3 & x4 & x5 & x6 & F2 & fc2 & ->).
  rewrite (hz_EU OK) in ST4, PR4. rewrite FRS2, LV2 in PR4.
  assert (LVI : forall e, In e live0 -> In e ((zb, nZ_of n) :: live0)) by (intros e He; right; exact He).
  assert (HM4 : HMc Σ3 m4).
  { apply (hm_step OK Σ2 Σ3 m3 m4 HM3 ART4 MI4 ST4). apply (core_of_pres_fp OK _ _ m3 m4 PR4 LVI). intros x Hx. cbn [outside].
    pose proof (core_not_chunk AF OK Σ2 m3 _ zb (nZ_of n) ART3 S2 ltac:(left; reflexivity) x Hx). pose proof (core_not_cells OK x Hx). lia. }
  assert (S4 : HSc Σ3 [(zb, nZ_of n)]) by (split; [rewrite LV3; exact LV2| split; [rewrite FRS3; exact FRS2| rewrite SP3; exact SP2]]).
  assert (NOJ4 : rw_cells bsegs m4 (Fr + 48) [CB 8 j6]).
  { apply (rw_cells_agree_nw bsegs m3 m4 _ _ NOJ3). apply (agree_of_pres_fp _ _ _ _ _ _ _ PR4). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [right; right; right; left; exists Fr, 0%nat; split; [left; reflexivity| change (fs_size 0) with 64; lia]|].
    cbn [outside]. pose proof (hs_chunk_frame AF ART3 S2 (or_introl eq_refl)) as CF. lia. }
  exact (hz_mid_cps Σ3 m4 zb rc dlv j6 c7 c8 x0 x1 x2 f1 f2 f3 f4 f5 f6 f7 x3 x4 x5 x6 F2 fc2 HM4 S4 DLC NOJ4 RES ltac:(ul) T cf4 Hc4' Hk).
Qed.

End Front.

(* [comment removed for export] *)
Section Harness.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis MAL : malloc_contract RT.
Hypothesis MAL0 : malloc0_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis MCMP : memcmp_icontract RT.
Hypothesis B2BC : b2bc_cps RT LIB enc_ok.
Hypothesis B2BD : b2bd_cps RT LIB dec_ok.
Hypothesis RTW : round_trip_weak enc_ok dec_ok.

Local Ltac ul := unfold B2B_STACK, B2B_LIVE, B2BD_COST, B2BC_COST, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt bsegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

Local Notation r33 f := (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* [comment removed for export] *)
Lemma hz_entry_cps : forall (Σ : rts RT) PMc (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m m1 : mem) (d : Z) (bs : list byte) (p0 n0 spa : Z)
    (z0 : word) (j8 : list byte) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word) F fc,
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6094d8 -> cra = Z_to_bv 64 RA_HARN -> fp_stop usp (bv_unsigned c0) ->
  rt_frames RT Σ = [] -> (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) -> Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp <= rt_sp0 RT Σ -> usp mod 16 = 0 ->
  (spa = usp + -128 \/ spa = usp + -144) -> spa mod 32 = 0 ->
  0 < d -> d + Z.of_nat (length bs) <= rt_sp0 RT Σ - STACK_WIN -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  (bs = [] \/ (In (p0, n0) (rt_live RT Σ) /\ p0 <= d /\ d + Z.of_nat (length bs) <= p0 + n0)) -> LIB m -> ART RT Σ m ->
  munch [(spa, usp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo spa ->
  rw_cells bsegs m1 (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  (spa = usp + -128 \/ (spa = usp + -144 /\ exists jg : list byte, rw_cells bsegs m1 (usp + -144) [CB 16 jg])) ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st (Z_to_bv 64 0x81374) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa)
             (Z_to_bv 64 64) a1' a2' a3' a4' a5' a6' a7' c2 (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 d) c5 c6 c7 c8 (Z_to_bv 64 SHB) c10 c11 u3 u4 u5 u6
             F fc (e_stack_malloc 0) m1)))
    (HQ RT LIB Σ PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m).
Proof using AF LIB_loc SM0 MAL MAL0 FRE MCMP B2BC B2BD RTW.
  intros Σ PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m m1 d bs p0 n0 spa z0 j8 u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 F fc
    FDO MST TP RAH S0F FRS0 POS LVB CRB LOW LOR SPT SPS SPA SPA1 SPA2 D0 DHI NB INB INP LIB0 ART0 MU1 WM1 MI1 ST1 FR1 GAP1 T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (GS : lo <= spa /\ spa + 128 <= usp /\ usp <= spa + 144) by ul.
  assert (EU : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; ul).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 spa ART0 ltac:(lia)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T c _ Hc _).
  { eapply (r33 (SM0 Σ PMc) m1 64 lo); try reflexivity.
    - exact FDO.
    - exact MST.
    - left; reflexivity.
    - exact TP.
    - change (fs_size 0) with 64. lia.
    - rewrite FRS0. cbn. unfold FRAMES_MAX. lia.
    - ul.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite EU. split; [exact ST1|]. split; [exact LOW|]. split; [ul|]. split; [ul|]. Z.div_mod_to_equations. lia. }
  intros cf2 (Σ1 & Fr & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FUT).
  destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PR2 & WF2 & WS2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU in ST2, PR2. rewrite FRS0 in FRS1, PR2.
  change (fs_size 0) with 64 in WF2, WS2, FUT. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  assert (INF : In (Fr, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 Fr 0 ART2 INF) as (_ & FR1' & _ & _). change (fs_size 0) with 64 in FR1'. rewrite SP1 in FR1'.
  pose proof (af_frames_align RT AF Σ1 m2 Fr 0 ART2 INF) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ1 m2 Fr 0 ART2 INF) as FPL. change (fs_size 0) with 64 in FPL.
  assert (OK : hz_ok RT LIB Σ PMc cra tp c0 usp lo m d bs p0 n0 spa Fr).
  { constructor; try assumption; [lia|].
    intros x Hx. pose proof (newframe_apart RT AF Σ Σ1 m2 Fr 0 usp x ART2 ltac:(rewrite FRS1, FRS0; reflexivity) LV1 SP1 ltac:(lia)) as NA.
    rewrite FRS0 in NA. change (fs_size 0) with 64 in NA. exact (NA Hx). }
  (* [comment removed for export] *)
  assert (AGC : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) [] spa x) -> agree_on P m1 m2).
  { intros P HP. exact (agree_of_pres _ _ _ _ _ _ PR2 HP). }
  assert (PR02 : agree_on (ACL RT Σ usp) m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [| exact I]. intros Hs.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; [lia| pose proof (client_static_range x Hx); ul|
        destruct Hx as (q & k & Hq & Hk'); pose proof (af_live_range RT AF Σ m q k ART0 Hq) as (_ & R & _); lia|
        destruct Hx as (f & k & [] & _)| destruct Hx as (f & k & [] & _)].
    - apply AGC. intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| lia]. }
  assert (AGS : forall a k, spa <= a -> a + k <= usp -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k A1 A2. apply AGC. intros x Hx. left. ul. }
  exact (hz_front_cps RT LIB enc_ok dec_ok AF LIB_loc MAL MAL0 FRE MCMP B2BC B2BD RTW Σ PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m d bs p0 n0 spa Fr OK
           Σ1 m2 z0 j8 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 fc2 ART2 MI2 ST2 PR02
           ltac:(apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1); apply AGS; cbn [cells_size hz_frame csize Nat.add]; lia)
           ltac:(destruct GAP1 as [E|(E & jg & GP)]; [left; exact E| right; split; [exact E|]; exists jg; apply (rw_cells_agree_nw bsegs m1 m2 _ _ GP); apply AGS;
                 cbn [cells_size csize Nat.add]; lia])
           (conj LV1 (conj FRS1 SP1)) WF2 WS2 CR1 T cf2 Hc2' Hk).
Qed.

Theorem harness_ok : fuzz_one_cps RT LIB.
Proof using AF LIB_loc SM0 MAL MAL0 FRE MCMP B2BC B2BD RTW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FDO MST -> -> TP RAH
    (D0 & DHI) NB INB INPC FRS0 POS LVB CRB S0C LIB0 SSP0 ART0 MI0 ST0 LOW LOR SPT SPA SPS.
  intros T c Hc Hk.
  remember (bv_unsigned sp) as usp eqn:EUSP in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (rewrite EUSP; symmetry; apply Z_to_bv_bv_unsigned).
  subst sp. clear EUSP.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (INP : exists p0 n0, bs = [] \/ (In (p0, n0) (rt_live RT Σ) /\ p0 <= d /\ d + Z.of_nat (length bs) <= p0 + n0)).
  { destruct INPC as [(p0 & n0 & H)|E]; [exists p0, n0; right; exact H| exists 0, 0; left; exact E]. }
  destruct INP as (p0 & n0 & INP).
  assert (S0F : fp_stop usp (bv_unsigned s0)) by (unfold fp_stop; destruct S0C as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]).
  assert (HQF : forall cf, HQ RT LIB Σ PMc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m cf -> realizes bsegs cf T).
  { intros cf (Σ' & HA & LV' & FRS' & SP' & CR'). apply Hk. exists Σ'. rewrite FRS0.
    split; [exact HA| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]]. }
  assert (U32 : usp mod 32 = 0 \/ usp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
  destruct U32 as [U0|U16].
  - pose proof (hz_wA0 usp lo d (Z.of_nat (length bs)) ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul)
                  ltac:(ul) U0 (af_client_consts RT AF Σ m ART0) MI0) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & z0 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1)
                                               & Hc1'). clear Hc1.
    exact (hz_entry_cps Σ PMc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m m1 d bs p0 n0 (usp + -128) z0 j8 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F fc
             FDO MST TP RAH S0F FRS0 POS LVB CRB LOW LOR SPT SPS SPA (or_introl eq_refl) ltac:(clear - U0; Z.div_mod_to_equations; lia) D0 DHI NB INB INP LIB0 ART0
             ltac:(replace (usp + -128) with (usp - 128) by lia; exact MU1) WM1 MI1 ST1 FR1 (or_introl eq_refl) T cf1 Hc1' HQF).
  - pose proof (hz_wA16 usp lo d (Z.of_nat (length bs)) ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul)
                  ltac:(ul) U16 (af_client_consts RT AF Σ m ART0) MI0) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & z0 & jg & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1)
                                               & Hc1'). clear Hc1.
    change (CB 16 jg :: hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) with ([CB 16 jg] ++ hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) in FR1.
    apply rw_cells_app in FR1 as (GP & FR1). cbn [cells_size csize Nat.add] in FR1. replace (usp + -144 + Z.of_nat 16) with (usp + -128) in FR1 by lia.
    exact (hz_entry_cps Σ PMc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m m1 d bs p0 n0 (usp + -144) z0 j8 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F fc
             FDO MST TP RAH S0F FRS0 POS LVB CRB LOW LOR SPT SPS SPA (or_intror eq_refl) ltac:(clear - U16; Z.div_mod_to_equations; lia) D0 DHI NB INB INP LIB0 ART0
             ltac:(replace (usp + -144) with (usp - 144) by lia; exact MU1) WM1 MI1 ST1 FR1 (or_intror (conj eq_refl (ex_intro _ jg GP))) T cf1 Hc1' HQF).
Qed.

End Harness.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow IcptSpec2 RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2
  L_harnw1 L_harnw2 L_harnw3 L_harnw4 L_harnw5 L_harn1 L_harn2 L_harn3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma hz_frame_split : forall (m : mem) a z0 j8 (r : list cell), rw_cells asegs m a (C8 z0 :: CB 24 j8 :: r) ->
  exists ja jb jc, rw_cells asegs m a [C8 z0] /\ rw_cells asegs m (a + 8) [CB 8 ja] /\ rw_cells asegs m (a + 16) [CB 8 jb] /\ rw_cells asegs m (a + 24) [CB 8 jc]
                   /\ rw_cells asegs m (a + 32) r.
Proof.
  intros m a z0 j8 r H.
  apply (rw_cells_split_CB asegs m a [C8 z0] 24 j8 r [8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  exists (firstn 8 j8), (firstn 8 (skipn 8 j8)), (firstn 8 (skipn 8 (skipn 8 j8))).
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H.
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H. replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H by lia.
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H. replace (a + 16 + Z.of_nat 8) with (a + 24) in H by lia.
  split; [exact (rw_cells_head m _ _ _ H)|]. apply rw_cells_tail in H. cbn [csize] in H. replace (a + 24 + Z.of_nat 8) with (a + 32) in H by lia. exact H.
Qed.

Lemma hz_frame_join : forall (m : mem) a z0 X1 X2 X3 (r : list cell), csize X1 = 8%nat -> csize X2 = 8%nat -> csize X3 = 8%nat ->
  rw_cells asegs m a [C8 z0] -> rw_cells asegs m (a + 8) [X1] -> rw_cells asegs m (a + 16) [X2] -> rw_cells asegs m (a + 24) [X3] -> rw_cells asegs m (a + 32) r ->
  exists j8, rw_cells asegs m a (C8 z0 :: CB 24 j8 :: r).
Proof.
  intros m a z0 X1 X2 X3 r S1 S2 S3 H0 H1 H2 H3 HR. exists (cells_bytes [X1; X2; X3]).
  assert (HJ : rw_cells asegs m a ([C8 z0] ++ [X1] ++ [X2] ++ [X3] ++ r)).
  { apply rw_cells_app. split; [exact H0|]. cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [exact H1|]. cbn [cells_size Nat.add]. rewrite S1.
    apply rw_cells_app. split; [replace (a + Z.of_nat 8 + Z.of_nat (8 + 0)) with (a + 16) by lia; exact H2|]. cbn [cells_size Nat.add]. rewrite S2.
    apply rw_cells_app. split; [replace (a + Z.of_nat 8 + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) with (a + 24) by lia; exact H3|]. cbn [cells_size Nat.add]. rewrite S3.
    replace (a + Z.of_nat 8 + Z.of_nat (8 + 0) + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) with (a + 32) by lia. exact HR. }
  apply (rw_cells_recast' m a _ _ HJ).
  - pose proof (proj1 (proj1 H1)) as (W1 & _). pose proof (proj1 (proj1 H2)) as (W2 & _). pose proof (proj1 (proj1 H3)) as (W3 & _). pose proof (proj1 (proj1 HR)) as WR.
    split; [exact I|]. split; [| exact WR]. cbn [cell_wf]. rewrite (cells_bytes_length [X1; X2; X3]) by (cbn [cells_wf]; tauto).
    cbn [cells_size]. rewrite S1, S2, S3. reflexivity.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

Section Front.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis MAL : malloc_contract RT.
Hypothesis MAL0 : malloc0_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis MCMP : memcmp_icontract RT.
Hypothesis B2BC : b2bc_cps RT LIB enc_ok.
Hypothesis B2BD : b2bd_cps RT LIB dec_ok.
Hypothesis RTW : round_trip_weak enc_ok dec_ok.

Variables (Σ0 : rts RT) (PMc : Model -> Prop) (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m0 : mem) (d : Z) (bs : list byte)
          (p0 n0 spa Fr : Z).
Local Notation n := (Z.of_nat (length bs)).
Local Notation live0 := (rt_live RT Σ0).
Local Notation OKT := (hz_ok RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr).
Local Notation HMc := (HM RT Σ0 cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 spa Fr).
Local Notation HSc := (HS RT Σ0 Fr).
Local Notation HQc := (HQ RT LIB Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0).
Hypothesis OK : OKT.

Local Ltac ul := unfold B2B_STACK, B2B_LIVE, B2BD_COST, B2BC_COST, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt asegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

Local Notation r33 f := (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* [comment removed for export] *)
Lemma harn_cost : forall k, 0 <= k < 2^26 -> 1 + mcost (nZ_of k) + B2BC_COST + mcost (2 * k) + B2BD_COST <= FUZZ_COST.
Proof.
  intros k Hk. unfold mcost, nZ_of, B2BC_COST, B2BD_COST, FUZZ_COST.
  assert (k / 100 <= k) by (apply Z.div_le_upper_bound; lia).
  destruct (k + 600 + k / 100 <=? 64512); destruct (2 * k <=? 64512); lia.
Qed.

Lemma mcost_nonneg : forall k, 0 <= k -> 0 <= mcost k.
Proof. intros k Hk. unfold mcost. destruct (k <=? 64512); lia. Qed.

(* [comment removed for export] *)
Lemma hz_mid_cps : forall (Σ : rts RT) (m : mem) zb rc dlv (j6 : list byte) (s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(zb, nZ_of n)] ->
  rw_cells asegs m (Fr + 32) [C4 (Z_to_bv 64 dlv)] -> rw_cells asegs m (Fr + 48) [CB 8 j6] ->
  ((rc = 0 /\ exists str, enc_ok bs (bs_of n) (wf_of n) str /\ dlv = Z.of_nat (length str) /\ dlv <= nZ_of n /\ bytes_at asegs m zb str) \/ (-9 <= rc < 0)) ->
  rt_credit RT Σ0 - FUZZ_COST + mcost (2 * n) + B2BD_COST <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 RA_B2BC) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 RA_B2BC)) fc None m (seg_rom asegs)))) HQc.
Proof using OK AF LIB_loc MAL MAL0 FRE MCMP B2BD RTW.
  intros Σ m zb rc dlv j6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S NZC NOJ RES CRX T c Hc Hk.
  pose proof H as (ART0 & MI0 & ST0 & _). pose proof S as (LV & FRS & SP0).
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FLO OK) as FLO. pose proof (hz_NB OK) as NB. pose proof (nZ_bound n ltac:(lia)) as NZB. pose proof (hz_CRB OK) as CRB.
  pose proof (mcost_nonneg (2 * n) ltac:(lia)) as MC0.
  assert (INZ : In (zb, nZ_of n) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m zb (nZ_of n) ART0 INZ) as (ZB0 & ZBH & _). rewrite SP0 in ZBH. pose proof (hz_LOW OK) as LOW. pose proof (hz_SP0R OK) as SP0R.
  destruct RES as [(-> & str & ENC & -> & DLB & ZBB)|RCN].
  - (* [comment removed for export] *)
    pose proof (hz_wD usp spa Fr d n zb j6 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 c11 t3 t4 t5 t6 F fc m ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ul) NOJ MI0) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & j7 & -> & MU1 & WM1 & MI1 & NOC1) & Hc1'). clear Hc1.
    assert (ART1 : ART RT Σ m1).
    { apply (hs_art_munch AF OK Σ _ _ m m1 ART0 S MU1 WM1). intros x H1 H2 H3. cbn [outside]. lia. }
    assert (HM1 : HMc Σ m1).
    { apply (hm_step OK Σ Σ m m1 H ART1 MI1 (stk_wmono' _ _ _ _ ST0 WM1)). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside].
      pose proof (core_not_cells OK x Hx). lia. }
    assert (NZC1 : rw_cells asegs m1 (Fr + 32) [C4 (Z_to_bv 64 (Z.of_nat (length str)))]).
    { apply (rw_cells_agree_nw asegs m m1 _ _ NZC). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. lia. }
    assert (ZBB1 : bytes_at asegs m1 zb str).
    { apply (bytes_at_agree asegs m m1 _ _ ZBB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside].
      pose proof (hs_chunk_frame AF ART0 S (or_introl eq_refl)) as CF. lia. }
    refine (cps_realizes asegs _ _ T cf1 (hz_malloc_step RT LIB AF MAL MAL0 Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK
                                            Σ m1 [(zb, nZ_of n)] (2 * n) 0x81a7c (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7
                                            (Z_to_bv 64 (Fr + 48)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc HM1 S ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia) ltac:(ul)) Hc1' _).
    intros cf2 (Σ1 & ob & Hc2 & S1 & CR1 & OB0 & OBT).
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & HM2 & PR2 & OBW) & Hc2').
    clear Hc2. rewrite LV in PR2.
    assert (AGF : forall a k, Fr <= a -> a + k <= Fr + 56 -> agree_on (fun x => a <= x < a + k) m1 m2).
    { intros a k A1 A2. apply (agree_of_pres _ _ _ _ _ _ PR2). intros x Hx. right; right; right; left. exists Fr, 0%nat. split; [left; reflexivity|].
      change (fs_size 0) with 64. lia. }
    exact (hz_dec_cps RT LIB enc_ok dec_ok AF LIB_loc FRE MCMP B2BD RTW Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK
             Σ1 m2 zb ob (Z.max (2 * n) 1) str j7 s7 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F1 fc1 HM2 S1 eq_refl OBW ENC DLB
             ltac:(apply (bytes_at_agree asegs m1 m2 _ _ ZBB1); apply (agree_of_pres _ _ _ _ _ _ PR2); intros x Hx; right; right; left; exists zb, (nZ_of n);
                   split; [left; reflexivity| lia])
             ltac:(apply (rw_cells_agree_nw asegs m1 m2 _ _ NZC1); apply AGF; cbn [cells_size csize Nat.add]; lia)
             ltac:(apply (rw_cells_agree_nw asegs m1 m2 _ _ NOC1); apply AGF; cbn [cells_size csize Nat.add]; lia)
             ltac:(ul) T cf2 Hc2' Hk).
  - (* [comment removed for export] *)
    pose proof (hz_wD_err usp spa Fr d n zb rc gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 c11 t3 t4 t5 t6 F fc m RCN ltac:(ul)) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1. destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & -> & Hc1'). clear Hc1.
    exact (hz_tail_cps RT LIB AF LIB_loc FRE Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK Σ m zb (nZ_of n)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc H S ltac:(lia) ltac:(ul) T cf1 Hc1' Hk).
Qed.

(* [comment removed for export] *)
Lemma hz_front_cps : forall (Σ1 : rts RT) (m : mem) (z0 : word) (j8 : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  ART RT Σ1 m -> mem_inv asegs m -> stk asegs m lo spa -> agree_on (ACL RT Σ0 usp) m0 m ->
  rw_cells asegs m (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  (spa = usp + -128 \/ (spa = usp + -144 /\ exists jg : list byte, rw_cells asegs m (usp + -144) [CB 16 jg])) ->
  HSc Σ1 [] -> wr_at asegs m Fr 56 -> wr_at asegs m (shad Fr) 8 -> rt_credit RT Σ1 = rt_credit RT Σ0 - 1 ->
  cps asegs (ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x81928) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 Fr) a1 a2 a3 a4 a5 a6 a7
             c2 (Z_to_bv 64 n) (Z_to_bv 64 d) c5 c6 c7 c8 (Z_to_bv 64 SHB) c10 c11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 0x81928)) fc None m (seg_rom asegs)))) HQc.
Proof using OK AF LIB_loc MAL MAL0 FRE MCMP B2BC B2BD RTW.
  intros Σ1 m z0 j8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc ART1 MI1 ST1 PR1 FR1 GAP1 S1 WF WS CR1 T c Hc Hk.
  pose proof S1 as (LV1 & FRS1 & SP1). cbn [app] in LV1.
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST. pose proof (hz_F64 OK) as F64. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FPL OK) as FPL. pose proof (hz_FLO OK) as FLO. pose proof (hz_NB OK) as NB. pose proof (nZ_bound n ltac:(lia)) as NZB. pose proof (hz_CRB OK) as CRB.
  pose proof (hz_D0 OK) as D0. pose proof (hz_DHI OK) as DHI. pose proof (hz_SP0R OK) as SP0R. pose proof (hz_LOW OK) as LOW. pose proof (shad_F_lo OK) as SHLO.
  pose proof (harn_cost n ltac:(lia)) as COST. pose proof (mcost_nonneg (nZ_of n) ltac:(lia)) as MCZ. pose proof (mcost_nonneg (2 * n) ltac:(lia)) as MCO.
  destruct (wr_at_rw_CB m Fr 56 WF ltac:(lia)) as (jh & HDRJ). destruct (wr_at_rw_CB m (shad Fr) 8 WS ltac:(lia)) as (js & SHJ).
  (* [comment removed for export] *)
  unfold hz_frame in FR1. destruct (hz_frame_split m (usp + -128) z0 j8 _ FR1) as (ja & jb & jc & FA & FB1 & FB2 & FB3 & FRR).
  replace (usp + -128 + 8) with (usp + -120) in FB1 by lia. replace (usp + -128 + 16) with (usp + -112) in FB2 by lia.
  replace (usp + -128 + 24) with (usp + -104) in FB3 by lia. replace (usp + -128 + 32) with (usp + -96) in FRR by lia.
  assert (SLOT : exists jsl, rw_cells asegs m (spa + 24) [CB 8 jsl]).
  { destruct (hz_SPA1 OK) as [E|E]; rewrite E; [exists jc; replace (usp + -128 + 24) with (usp + -104) by lia; exact FB3|
                                                  exists ja; replace (usp + -144 + 24) with (usp + -120) by lia; exact FB1]. }
  destruct SLOT as (jsl & SLOT).
  pose proof (hz_wB usp spa Fr d n jh js jsl gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 c2 c5 c6 c7 c8 c10 c11 t3 t4 t5 t6 F fc m ltac:(lia) F64 FPL ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(ul) ltac:(lia) HDRJ SHJ SLOT MI1) as W.
  to_cps W c Hc Σ1 MST. intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m2 & h0 & h1 & h2 & b1 & b2 & b3 & b4 & b5 & j3 & j5 & j6 & -> & MU2 & WM2 & MI2 & FC2 & SH2 & SL2) & Hc1').
  clear Hc1.
  assert (ART2 : ART RT Σ1 m2).
  { apply (hs_art_munch AF OK Σ1 _ _ m m2 ART1 S1 MU2 WM2). intros x H1 H2 H3. cbn [outside]. lia. }
  assert (AGS : forall a k, spa <= a -> a + k <= usp -> (a + k <= spa + 24 \/ spa + 32 <= a) -> agree_on (fun x => a <= x < a + k) m m2).
  { intros a k A1 A2 A3. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [outside]. lia. }
  (* [comment removed for export] *)
  assert (FR2 : exists j8', rw_cells asegs m2 (usp + -128) (hz_frame (C8 z0) j8' c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)).
  { unfold hz_frame.
    assert (FA2 : rw_cells asegs m2 (usp + -128) [C8 z0]) by (apply (rw_cells_agree_nw asegs m m2 _ _ FA); apply AGS; cbn [cells_size csize Nat.add]; lia).
    assert (FB22 : rw_cells asegs m2 (usp + -112) [CB 8 jb]) by (apply (rw_cells_agree_nw asegs m m2 _ _ FB2); apply AGS; cbn [cells_size csize Nat.add]; lia).
    assert (FRR2 : rw_cells asegs m2 (usp + -96) [C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra])
      by (apply (rw_cells_agree_nw asegs m m2 _ _ FRR); apply AGS; cbn [cells_size csize Nat.add]; lia).
    destruct (hz_SPA1 OK) as [E|E].
    - assert (FB12 : rw_cells asegs m2 (usp + -120) [CB 8 ja]) by (apply (rw_cells_agree_nw asegs m m2 _ _ FB1); apply AGS; cbn [cells_size csize Nat.add]; lia).
      rewrite E in SL2. replace (usp + -128 + 24) with (usp + -104) in SL2 by lia.
      apply (hz_frame_join m2 (usp + -128) z0 (CB 8 ja) (CB 8 jb) (C8 (Z_to_bv 64 Fr))); try reflexivity; try assumption.
      + replace (usp + -128 + 8) with (usp + -120) by lia. exact FB12.
      + replace (usp + -128 + 16) with (usp + -112) by lia. exact FB22.
      + replace (usp + -128 + 24) with (usp + -104) by lia. exact SL2.
      + replace (usp + -128 + 32) with (usp + -96) by lia. exact FRR2.
    - assert (FB32 : rw_cells asegs m2 (usp + -104) [CB 8 jc]) by (apply (rw_cells_agree_nw asegs m m2 _ _ FB3); apply AGS; cbn [cells_size csize Nat.add]; lia).
      rewrite E in SL2. replace (usp + -144 + 24) with (usp + -120) in SL2 by lia.
      apply (hz_frame_join m2 (usp + -128) z0 (C8 (Z_to_bv 64 Fr)) (CB 8 jb) (CB 8 jc)); try reflexivity; try assumption.
      + replace (usp + -128 + 8) with (usp + -120) by lia. exact SL2.
      + replace (usp + -128 + 16) with (usp + -112) by lia. exact FB22.
      + replace (usp + -128 + 24) with (usp + -104) by lia. exact FB32.
      + replace (usp + -128 + 32) with (usp + -96) by lia. exact FRR2. }
  destruct FR2 as (j8' & FR2).
  (* [comment removed for export] *)
  change [C8 h0; C8 h1; C8 h2; CB 8 j3; C4 (Z_to_bv 64 (nZ_of n)); CB 12 j5; CB 8 j6]
    with ([C8 h0] ++ [C8 h1; C8 h2; CB 8 j3] ++ [C4 (Z_to_bv 64 (nZ_of n))] ++ [CB 12 j5] ++ [CB 8 j6]) in FC2.
  apply rw_cells_app in FC2 as (HDR2 & FC2). apply rw_cells_app in FC2 as (_ & FC2). apply rw_cells_app in FC2 as (NZC2 & FC2).
  apply rw_cells_app in FC2 as (_ & NOJ2). cbn [cells_size csize Nat.add] in NZC2, NOJ2.
  replace (Fr + Z.of_nat 8 + Z.of_nat 24) with (Fr + 32) in NZC2 by lia. replace (Fr + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 4 + Z.of_nat 12) with (Fr + 48) in NOJ2 by lia.
  assert (HM2 : HMc Σ1 m2).
  { split; [exact ART2|]. split; [exact MI2|]. split; [exact (stk_wmono' _ _ _ _ ST1 WM2)|].
    split; [apply (agree_trans _ m0 m m2 PR1); apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [outside];
            destruct (hz_FAP OK x Hx) as (A1 & A2); rewrite (shad_F64 OK) in A2;
            assert (~ (spa + 24 <= x < spa + 32)) by (intros Hs; destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]];
              [lia| pose proof (client_static_range x Hx); ul| destruct Hx as (q & k & Hq & Hk'); pose proof (af_live_range RT AF Σ1 m q k ART1 ltac:(rewrite LV1; exact Hq)) as (_ & R & _);
                rewrite SP1 in R; lia| destruct Hx as (f & k & [] & _)| destruct Hx as (f & k & [] & _)]); lia|].
    split; [exists z0, j8'; exact FR2|].
    split; [destruct GAP1 as [E|(E & jg & GP)]; [left; exact E| right; split; [exact E|]; exists jg; apply (rw_cells_agree_nw asegs m m2 _ _ GP); apply AGS;
            cbn [cells_size csize Nat.add]; lia]|].
    split; [exists h0; exact HDR2| exact SH2]. }
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T cf1 (hz_malloc_step RT LIB AF MAL MAL0 Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK
                                          Σ1 m2 [] (nZ_of n) 0x819e8 (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) c6 c7 c8
                                          _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc HM2 S1 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia) ltac:(ul)) Hc1' _).
  intros cf2 (Σ2 & zb & Hc2 & S2 & CR2 & ZB0 & ZBT). replace (Z.max (nZ_of n) 1) with (nZ_of n) in * by lia.
  destruct (ASTA_unpack RT Σ2 _ _ cf2 Hc2) as (ms2 & (m3 & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & HM3 & PR3 & ZBW) & Hc2').
  clear Hc2. rewrite LV1 in PR3. pose proof HM3 as (ART3 & MI3 & ST3 & _ & _ & _ & _ & SH3). pose proof S2 as (LV2 & FRS2 & SP2). cbn [app] in LV2.
  assert (AGF : forall a k, Fr <= a -> a + k <= Fr + 56 -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k A1 A2. apply (agree_of_pres _ _ _ _ _ _ PR3). intros x Hx. right; right; right; left. exists Fr, 0%nat. split; [left; reflexivity|].
    change (fs_size 0) with 64. lia. }
  assert (NZC3 : rw_cells asegs m3 (Fr + 32) [C4 (Z_to_bv 64 (nZ_of n))]) by (apply (rw_cells_agree_nw asegs m2 m3 _ _ NZC2); apply AGF; cbn [cells_size csize Nat.add]; lia).
  assert (NOJ3 : rw_cells asegs m3 (Fr + 48) [CB 8 j6]) by (apply (rw_cells_agree_nw asegs m2 m3 _ _ NOJ2); apply AGF; cbn [cells_size csize Nat.add]; lia).
  (* [comment removed for export] *)
  pose proof (hz_wC usp spa Fr d n zb gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c6 c7 c8 c11 w3 w4 w5 w6 F1 fc1 m3 ltac:(lia) ltac:(ul) MI3) as W.
  to_cps W cf2 Hc2' Σ2 MST. intros cf3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ cf3 Hc3) as (ms3 & (a7' & ->) & Hc3'). clear Hc3.
  destruct (wr_at_rw_CB m3 zb (nZ_of n) ZBW ltac:(lia)) as (junk & ZBJ).
  destruct (hz_sh0_parts m3 (shad Fr) SH3) as (SH4 & _).
  assert (ESH : shad (Fr + 32) = shad Fr + 4) by (unfold shad; Z.div_mod_to_equations; lia).
  assert (INZ : In (zb, nZ_of n) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T cf3 _ Hc3' _).
  { eapply (r33 (B2BC Σ2 PMc) m3 zb (Fr + 32) d bs junk lo); try reflexivity.
    - exact (hz_FDO OK).
    - exact MST.
    - exact (hz_TP OK).
    - lia.
    - ul.
    - exact (hm_payload OK Σ2 m3 HM3).
    - destruct (hz_INP OK) as [E|(IN0 & P0 & P1)]; [right; exact E| left]. exists p0, n0. split; [rewrite LV2; right; exact IN0|]. split; [lia|]. split; [lia|].
      intros E. injection E as E1 E2. exact (hs_fresh AF OK Σ2 m3 _ zb (nZ_of n) ART3 S2 (or_introl eq_refl) ltac:(lia) (p0, n0) IN0 E1).
    - exact INZ.
    - exact ZBJ.
    - exists Fr, 0%nat. split; [rewrite FRS2; left; reflexivity|]. change (fs_size 0) with 64. lia.
    - exact NZC3.
    - Z.div_mod_to_equations. lia.
    - rewrite ESH. exact SH4.
    - intros p k Hin. rewrite LV2 in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; lia| pose proof (hz_POS OK p k Hin); lia].
    - rewrite LV2. cbn [length]. pose proof (hz_LVB OK). ul.
    - rewrite FRS2. cbn. unfold B2B_FRAMES, FRAMES_MAX. lia.
    - ul.
    - exact (hm_record OK Σ2 m3 HM3).
    - exact (hm_lib LIB_loc OK Σ2 m3 HM3).
    - exact ART3.
    - exact MI3.
    - rewrite (hz_EU OK). exact ST3.
    - rewrite SP2. exact LOW.
    - rewrite (hz_EU OK). pose proof (hz_LOR OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPT OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPA2 OK). Z.div_mod_to_equations. lia.
    - rewrite (hz_EU OK), SP2. pose proof (hz_SPS OK). lia. }
  intros cf4 (Σ3 & rc & dlv & Hc4 & LV3 & FRS3 & SP3 & CR3).
  destruct (ASTA_unpack RT Σ3 _ _ cf4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PR4 & DLC & _ & RES) & Hc4'). clear Hc4.
  destruct RS4 as (x0 & x1 & x2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & x3 & x4 & x5 & x6 & F2 & fc2 & ->).
  rewrite (hz_EU OK) in ST4, PR4. rewrite FRS2, LV2 in PR4.
  assert (LVI : forall e, In e live0 -> In e ((zb, nZ_of n) :: live0)) by (intros e He; right; exact He).
  assert (HM4 : HMc Σ3 m4).
  { apply (hm_step OK Σ2 Σ3 m3 m4 HM3 ART4 MI4 ST4). apply (core_of_pres_fp OK _ _ m3 m4 PR4 LVI). intros x Hx. cbn [outside].
    pose proof (core_not_chunk AF OK Σ2 m3 _ zb (nZ_of n) ART3 S2 ltac:(left; reflexivity) x Hx). pose proof (core_not_cells OK x Hx). lia. }
  assert (S4 : HSc Σ3 [(zb, nZ_of n)]) by (split; [rewrite LV3; exact LV2| split; [rewrite FRS3; exact FRS2| rewrite SP3; exact SP2]]).
  assert (NOJ4 : rw_cells asegs m4 (Fr + 48) [CB 8 j6]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ NOJ3). apply (agree_of_pres_fp _ _ _ _ _ _ _ PR4). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [right; right; right; left; exists Fr, 0%nat; split; [left; reflexivity| change (fs_size 0) with 64; lia]|].
    cbn [outside]. pose proof (hs_chunk_frame AF ART3 S2 (or_introl eq_refl)) as CF. lia. }
  exact (hz_mid_cps Σ3 m4 zb rc dlv j6 c7 c8 x0 x1 x2 f1 f2 f3 f4 f5 f6 f7 x3 x4 x5 x6 F2 fc2 HM4 S4 DLC NOJ4 RES ltac:(ul) T cf4 Hc4' Hk).
Qed.

End Front.

(* [comment removed for export] *)
Section Harness.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis MAL : malloc_contract RT.
Hypothesis MAL0 : malloc0_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis MCMP : memcmp_icontract RT.
Hypothesis B2BC : b2bc_cps RT LIB enc_ok.
Hypothesis B2BD : b2bd_cps RT LIB dec_ok.
Hypothesis RTW : round_trip_weak enc_ok dec_ok.

Local Ltac ul := unfold B2B_STACK, B2B_LIVE, B2BD_COST, B2BC_COST, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt asegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

Local Notation r33 f := (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* [comment removed for export] *)
Lemma hz_entry_cps : forall (Σ : rts RT) PMc (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m m1 : mem) (d : Z) (bs : list byte) (p0 n0 spa : Z)
    (z0 : word) (j8 : list byte) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word) F fc,
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x5fc0d8 -> cra = Z_to_bv 64 RA_HARN -> fp_stop usp (bv_unsigned c0) ->
  rt_frames RT Σ = [] -> (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) -> Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp <= rt_sp0 RT Σ -> usp mod 16 = 0 ->
  (spa = usp + -128 \/ spa = usp + -144) -> spa mod 32 = 0 ->
  0 < d -> d + Z.of_nat (length bs) <= rt_sp0 RT Σ - STACK_WIN -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  (bs = [] \/ (In (p0, n0) (rt_live RT Σ) /\ p0 <= d /\ d + Z.of_nat (length bs) <= p0 + n0)) -> LIB m -> ART RT Σ m ->
  munch [(spa, usp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo spa ->
  rw_cells asegs m1 (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  (spa = usp + -128 \/ (spa = usp + -144 /\ exists jg : list byte, rw_cells asegs m1 (usp + -144) [CB 16 jg])) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st (Z_to_bv 64 0x81928) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa)
             (Z_to_bv 64 64) a1' a2' a3' a4' a5' a6' a7' c2 (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 d) c5 c6 c7 c8 (Z_to_bv 64 SHB) c10 c11 u3 u4 u5 u6
             F fc (e_stack_malloc 0) m1)))
    (HQ RT LIB Σ PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m).
Proof using AF LIB_loc SM0 MAL MAL0 FRE MCMP B2BC B2BD RTW.
  intros Σ PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m m1 d bs p0 n0 spa z0 j8 u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 F fc
    FDO MST TP RAH S0F FRS0 POS LVB CRB LOW LOR SPT SPS SPA SPA1 SPA2 D0 DHI NB INB INP LIB0 ART0 MU1 WM1 MI1 ST1 FR1 GAP1 T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (GS : lo <= spa /\ spa + 128 <= usp /\ usp <= spa + 144) by ul.
  assert (EU : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; ul).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 spa ART0 ltac:(lia)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (r33 (SM0 Σ PMc) m1 64 lo); try reflexivity.
    - exact FDO.
    - exact MST.
    - left; reflexivity.
    - exact TP.
    - change (fs_size 0) with 64. lia.
    - rewrite FRS0. cbn. unfold FRAMES_MAX. lia.
    - ul.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite EU. split; [exact ST1|]. split; [exact LOW|]. split; [ul|]. split; [ul|]. Z.div_mod_to_equations. lia. }
  intros cf2 (Σ1 & Fr & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FUT).
  destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PR2 & WF2 & WS2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU in ST2, PR2. rewrite FRS0 in FRS1, PR2.
  change (fs_size 0) with 64 in WF2, WS2, FUT. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  assert (INF : In (Fr, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 Fr 0 ART2 INF) as (_ & FR1' & _ & _). change (fs_size 0) with 64 in FR1'. rewrite SP1 in FR1'.
  pose proof (af_frames_align RT AF Σ1 m2 Fr 0 ART2 INF) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ1 m2 Fr 0 ART2 INF) as FPL. change (fs_size 0) with 64 in FPL.
  assert (OK : hz_ok RT LIB Σ PMc cra tp c0 usp lo m d bs p0 n0 spa Fr).
  { constructor; try assumption; [lia|].
    intros x Hx. pose proof (newframe_apart RT AF Σ Σ1 m2 Fr 0 usp x ART2 ltac:(rewrite FRS1, FRS0; reflexivity) LV1 SP1 ltac:(lia)) as NA.
    rewrite FRS0 in NA. change (fs_size 0) with 64 in NA. exact (NA Hx). }
  (* [comment removed for export] *)
  assert (AGC : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) [] spa x) -> agree_on P m1 m2).
  { intros P HP. exact (agree_of_pres _ _ _ _ _ _ PR2 HP). }
  assert (PR02 : agree_on (ACL RT Σ usp) m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [| exact I]. intros Hs.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; [lia| pose proof (client_static_range x Hx); ul|
        destruct Hx as (q & k & Hq & Hk'); pose proof (af_live_range RT AF Σ m q k ART0 Hq) as (_ & R & _); lia|
        destruct Hx as (f & k & [] & _)| destruct Hx as (f & k & [] & _)].
    - apply AGC. intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| lia]. }
  assert (AGS : forall a k, spa <= a -> a + k <= usp -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k A1 A2. apply AGC. intros x Hx. left. ul. }
  exact (hz_front_cps RT LIB enc_ok dec_ok AF LIB_loc MAL MAL0 FRE MCMP B2BC B2BD RTW Σ PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m d bs p0 n0 spa Fr OK
           Σ1 m2 z0 j8 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 fc2 ART2 MI2 ST2 PR02
           ltac:(apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1); apply AGS; cbn [cells_size hz_frame csize Nat.add]; lia)
           ltac:(destruct GAP1 as [E|(E & jg & GP)]; [left; exact E| right; split; [exact E|]; exists jg; apply (rw_cells_agree_nw asegs m1 m2 _ _ GP); apply AGS;
                 cbn [cells_size csize Nat.add]; lia])
           (conj LV1 (conj FRS1 SP1)) WF2 WS2 CR1 T cf2 Hc2' Hk).
Qed.

Theorem harness_ok : fuzz_one_cps RT LIB.
Proof using AF LIB_loc SM0 MAL MAL0 FRE MCMP B2BC B2BD RTW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FDO MST -> -> TP RAH
    (D0 & DHI) NB INB INPC FRS0 POS LVB CRB S0C LIB0 SSP0 ART0 MI0 ST0 LOW LOR SPT SPA SPS.
  intros T c Hc Hk.
  remember (bv_unsigned sp) as usp eqn:EUSP in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (rewrite EUSP; symmetry; apply Z_to_bv_bv_unsigned).
  subst sp. clear EUSP.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (INP : exists p0 n0, bs = [] \/ (In (p0, n0) (rt_live RT Σ) /\ p0 <= d /\ d + Z.of_nat (length bs) <= p0 + n0)).
  { destruct INPC as [(p0 & n0 & H)|E]; [exists p0, n0; right; exact H| exists 0, 0; left; exact E]. }
  destruct INP as (p0 & n0 & INP).
  assert (S0F : fp_stop usp (bv_unsigned s0)) by (unfold fp_stop; destruct S0C as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]).
  assert (HQF : forall cf, HQ RT LIB Σ PMc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m cf -> realizes asegs cf T).
  { intros cf (Σ' & HA & LV' & FRS' & SP' & CR'). apply Hk. exists Σ'. rewrite FRS0.
    split; [exact HA| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]]. }
  assert (U32 : usp mod 32 = 0 \/ usp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
  destruct U32 as [U0|U16].
  - pose proof (hz_wA0 usp lo d (Z.of_nat (length bs)) ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul)
                  ltac:(ul) U0 (af_client_consts RT AF Σ m ART0) MI0) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & z0 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1)
                                               & Hc1'). clear Hc1.
    exact (hz_entry_cps Σ PMc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m m1 d bs p0 n0 (usp + -128) z0 j8 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F fc
             FDO MST TP RAH S0F FRS0 POS LVB CRB LOW LOR SPT SPS SPA (or_introl eq_refl) ltac:(clear - U0; Z.div_mod_to_equations; lia) D0 DHI NB INB INP LIB0 ART0
             ltac:(replace (usp + -128) with (usp - 128) by lia; exact MU1) WM1 MI1 ST1 FR1 (or_introl eq_refl) T cf1 Hc1' HQF).
  - pose proof (hz_wA16 usp lo d (Z.of_nat (length bs)) ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul)
                  ltac:(ul) U16 (af_client_consts RT AF Σ m ART0) MI0) as W.
    to_cps W c Hc Σ MST. intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & z0 & jg & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1)
                                               & Hc1'). clear Hc1.
    change (CB 16 jg :: hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) with ([CB 16 jg] ++ hz_frame (C8 z0) j8 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) in FR1.
    apply rw_cells_app in FR1 as (GP & FR1). cbn [cells_size csize Nat.add] in FR1. replace (usp + -144 + Z.of_nat 16) with (usp + -128) in FR1 by lia.
    exact (hz_entry_cps Σ PMc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m m1 d bs p0 n0 (usp + -144) z0 j8 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F fc
             FDO MST TP RAH S0F FRS0 POS LVB CRB LOW LOR SPT SPS SPA (or_intror eq_refl) ltac:(clear - U16; Z.div_mod_to_equations; lia) D0 DHI NB INB INP LIB0 ART0
             ltac:(replace (usp + -144) with (usp - 144) by lia; exact MU1) WM1 MI1 ST1 FR1 (or_intror (conj eq_refl (ex_intro _ jg GP))) T cf1 Hc1' HQF).
Qed.

End Harness.
