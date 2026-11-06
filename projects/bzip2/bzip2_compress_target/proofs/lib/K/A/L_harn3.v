(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow IcptSpec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2 L_harnw1 L_harnw2 L_harnw5 L_harn1 L_harn2.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow IcptSpec2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw5.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn2.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section RoundTrip.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis FRE : free_contract RT.
Hypothesis MCMP : memcmp_icontract RT.
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

Lemma nZ_bound : forall k, 0 <= k < 2^26 -> 600 <= nZ_of k < 2^27.
Proof. intros k Hk. unfold nZ_of. assert (0 <= k / 100 <= k) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia. Qed.

(* [comment removed for export] *)
Lemma hz_dec_cps : forall (Σ : rts RT) (m : mem) zb ob oc (str j7 : list byte) (s7 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(ob, oc); (zb, nZ_of n)] -> oc = Z.max (2 * n) 1 -> wr_at bsegs m ob oc ->
  enc_ok bs (bs_of n) (wf_of n) str -> Z.of_nat (length str) <= nZ_of n -> bytes_at bsegs m zb str ->
  rw_cells bsegs m (Fr + 32) [C4 (Z_to_bv 64 (Z.of_nat (length str)))] -> rw_cells bsegs m (Fr + 48) [C4 (Z_to_bv 64 (2 * n)); CB 4 j7] ->
  rt_credit RT Σ0 - FUZZ_COST + B2BD_COST <= rt_credit RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 0x814c8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 ob) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x814c8)) fc None m (seg_rom bsegs)))) HQc.
Proof using OK AF LIB_loc FRE MCMP B2BD RTW.
  intros Σ m zb ob oc str j7 s7 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S OC OBW ENC DLB ZBB NZC NOC CRX T c Hc Hk.
  pose proof H as (ART0 & MI0 & ST0 & PR0 & _ & _ & _ & SH0). pose proof S as (LV & FRS & SP0).
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST. pose proof (hz_F64 OK) as F64. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FLO OK) as FLO. pose proof (hz_NB OK) as NB. pose proof (nZ_bound n ltac:(lia)) as NZB.
  assert (INZ : In (zb, nZ_of n) (rt_live RT Σ)) by (rewrite LV; right; left; reflexivity).
  assert (INO : In (ob, oc) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m ob oc ART0 INO) as (OB0 & OBH & _). pose proof (af_live_range RT AF Σ m zb (nZ_of n) ART0 INZ) as (ZB0 & ZBH & _).
  rewrite SP0 in OBH, ZBH. pose proof (hz_LOW OK) as LOW. pose proof (hz_SP0R OK) as SP0R.
  assert (NE : ob <> zb).
  { pose proof (af_live_disj RT AF Σ m zb (nZ_of n) ob oc [(ob, oc)] live0 ART0 LV ltac:(left; reflexivity)) as D. lia. }
  (* [comment removed for export] *)
  pose proof (hz_wE usp spa Fr d n zb ob (Z.of_nat (length str)) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 c11 t3 t4 t5 t6 F fc m ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(ul) ltac:(lia) NZC MI0) as W.
  to_cps W c Hc Σ MST. intros cf1 Hc1. destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & -> & Hc1'). clear Hc1.
  set (sm := n mod 2 =? 1).
  assert (ESM : n mod 2 = if sm then 1 else 0) by (unfold sm; destruct (Z.eqb_spec (n mod 2) 1) as [E|E]; [exact E| pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia]).
  rewrite ESM in Hc1'.
  destruct (wr_at_rw_CB m ob (2 * n) (wr_at_sub m ob oc ob (2 * n) OBW ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (junk & OBJ).
  destruct (hz_sh0_parts m (shad Fr) SH0) as (_ & SH6).
  assert (ESH : shad (Fr + 48) = shad Fr + 6) by (unfold shad; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T cf1 _ Hc1' _).
  { eapply (r33 (B2BD Σ PMc) m ob (Fr + 48) zb (2 * n) oc (nZ_of n) str junk sm lo); try reflexivity.
    - exact (hz_FDO OK).
    - exact MST.
    - exact (hz_TP OK).
    - lia.
    - exact DLB.
    - lia.
    - exact ZBB.
    - exact INZ.
    - exact INO.
    - lia.
    - exact NE.
    - exact OBJ.
    - exists Fr, 0%nat. split; [rewrite FRS; left; reflexivity|]. change (fs_size 0) with 64. lia.
    - exact (rw_cells_head m _ _ _ NOC).
    - Z.div_mod_to_equations. lia.
    - rewrite ESH. exact SH6.
    - intros p k Hin. rewrite LV in Hin. destruct Hin as [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia| pose proof (hz_POS OK p k Hin); lia].
    - rewrite LV. cbn [length app]. pose proof (hz_LVB OK). ul.
    - rewrite FRS. cbn. unfold B2B_FRAMES, FRAMES_MAX. lia.
    - pose proof (hz_CRB OK). ul.
    - exact (hm_record OK Σ m H).
    - exact (hm_lib LIB_loc OK Σ m H).
    - exact ART0.
    - exact MI0.
    - rewrite (hz_EU OK). exact ST0.
    - rewrite SP0. exact LOW.
    - rewrite (hz_EU OK). pose proof (hz_LOR OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPT OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPA2 OK). Z.div_mod_to_equations. lia.
    - rewrite (hz_EU OK), SP0. pose proof (hz_SPS OK). lia. }
  intros cf2 (Σ1 & rc & dlv & Hc2 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m1 & RS2 & (ART1 & MI1 & ST1) & PR1 & DLC & _ & RES) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->).
  rewrite (hz_EU OK) in ST1, PR1. rewrite FRS in PR1. rewrite LV in PR1 at 1.
  assert (LVI : forall e, In e live0 -> In e ((ob, oc) :: (zb, nZ_of n) :: live0)) by (intros e He; right; right; exact He).
  assert (H1 : HMc Σ1 m1).
  { apply (hm_step OK Σ Σ1 m m1 H ART1 MI1 ST1). apply (core_of_pres_fp OK _ _ m m1 PR1 LVI). intros x Hx. cbn [outside].
    pose proof (core_not_chunk AF OK Σ m _ ob oc ART0 S ltac:(left; reflexivity) x Hx). pose proof (core_not_cells OK x Hx). lia. }
  assert (S1 : HSc Σ1 [(ob, oc); (zb, nZ_of n)]) by (split; [rewrite LV1; exact LV| split; [rewrite FRS1; exact FRS| rewrite SP1; exact SP0]]).
  assert (CRX1 : rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ1) by lia.
  destruct RES as [(-> & out & DEC & DLV & DLVC & OBB)|RCN].
  - (* [comment removed for export] *)
    pose proof (RTW bs (bs_of n) (wf_of n) str sm (2 * n) out ltac:(lia) ENC DEC) as EO. subst out.
    assert (NOC1 : rw_cells bsegs m1 (Fr + 48) [C4 (Z_to_bv 64 n); CB 4 j7]).
    { change [C4 (Z_to_bv 64 n); CB 4 j7] with ([C4 (Z_to_bv 64 n)] ++ [CB 4 j7]). apply rw_cells_app. split; [rewrite <- DLV; exact DLC|].
      pose proof (rw_cells_tail m _ _ _ NOC) as TL. cbn [csize cells_size Nat.add] in TL |- *.
      apply (rw_cells_agree_nw bsegs m m1 _ _ TL). apply (agree_of_pres_fp _ _ _ _ _ _ _ PR1). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [right; right; right; left; exists Fr, 0%nat; split; [left; reflexivity| change (fs_size 0) with 64; lia]|].
      cbn [outside]. pose proof (hs_chunk_frame AF ART0 S (or_introl eq_refl)) as CF. lia. }
    pose proof (hz_wF usp spa Fr d n zb ob j7 gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c11 w3 w4 w5 w6 F1 fc1 m1 ltac:(lia) ltac:(lia) ltac:(lia) NOC1 MI1) as W.
    to_cps W cf2 Hc2' Σ1 MST. intros cf3 Hc3. destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
    (* [comment removed for export] *)
    assert (INO1 : In (ob, oc) (rt_live RT Σ1)) by (rewrite LV1; exact INO).
    pose proof (hz_DHI OK) as DHI. pose proof (hz_D0 OK) as D0.
    refine (cps_realizes bsegs _ _ T cf3 _ Hc3' _).
    { unfold hz_call. eapply (r33 (MCMP Σ1 PMc) m1 d ob bs bs lo); try reflexivity.
      - exact (hz_FDO OK).
      - exact MST.
      - ul.
      - ul.
      - lia.
      - exact (hm_payload OK Σ1 m1 H1).
      - exact OBB.
      - split; [| left; lia]. intros NP. destruct (hz_INP OK) as [E|(IN0 & P0 & P1)]; [rewrite E in NP; cbn in NP; lia|].
        assert (IN1 : In (p0, n0) (rt_live RT Σ1)) by (rewrite LV1, LV; apply LVI; exact IN0).
        split; [apply (acc_sub bsegs m1 p0 n0); [exact (proj2 (af_acc_live RT AF Σ1 m1 p0 n0 ART1 IN1))| lia| lia]|].
        left. exists p0, n0. split; [exact IN1| lia].
      - split; [| left; lia]. intros NP.
        split; [apply (acc_sub bsegs m1 ob oc); [exact (proj2 (af_acc_live RT AF Σ1 m1 ob oc ART1 INO1))| lia| lia]|].
        left. exists ob, oc. split; [exact INO1| lia].
      - exact ART1.
      - exact MI1.
      - exact (hm_call_ok OK Σ1 m1 _ H1 S1). }
    intros cf4 Hc4. unfold icpt_post in Hc4.
    destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m2 & RS4 & (ART2 & MI2 & _ & ST2) & PR2 & _) & Hc4'). clear Hc4.
    destruct RS4 as (x0 & x1 & x2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & x3 & x4 & x5 & x6 & F2 & fc2 & ->).
    rewrite (hz_EU OK) in ST2, PR2. rewrite FRS1, FRS, LV1, LV in PR2. cbn [app] in PR2. rewrite memcmp_res_refl in Hc4'.
    assert (H2 : HMc Σ1 m2).
    { apply (hm_step OK Σ1 Σ1 m1 m2 H1 ART2 MI2 ST2). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR2). intros x Hx.
      split; [exact (core_client OK _ LVI x Hx)| lia]. }
    pose proof (hz_wG usp spa Fr d n zb ob gp tp x0 x1 x2 f1 f2 f3 f4 f5 f6 f7 c11 x3 x4 x5 x6 F2 fc2 m2 ltac:(ul)) as W.
    to_cps W cf4 Hc4' Σ1 MST. intros cf5 Hc5. destruct (ASTA_unpack RT Σ1 _ _ cf5 Hc5) as (ms5 & <- & Hc5'). clear Hc5.
    exact (hz_free2_cps RT LIB AF LIB_loc FRE Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK Σ1 m2 zb (nZ_of n) ob oc
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 H2 S1 ltac:(lia) ltac:(lia) CRX1 T cf5 Hc5' Hk).
  - (* [comment removed for export] *)
    pose proof (hz_wF_err usp spa Fr d n zb ob rc gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c11 w3 w4 w5 w6 F1 fc1 m1 RCN ltac:(ul)) as W.
    to_cps W cf2 Hc2' Σ1 MST. intros cf3 Hc3. destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
    exact (hz_free2_cps RT LIB AF LIB_loc FRE Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK Σ1 m1 zb (nZ_of n) ob oc
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 H1 S1 ltac:(lia) ltac:(lia) CRX1 T cf3 Hc3' Hk).
Qed.

End RoundTrip.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow IcptSpec2 RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2
  L_harnw1 L_harnw2 L_harnw5 L_harn1 L_harn2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section RoundTrip.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis FRE : free_contract RT.
Hypothesis MCMP : memcmp_icontract RT.
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

Lemma nZ_bound : forall k, 0 <= k < 2^26 -> 600 <= nZ_of k < 2^27.
Proof. intros k Hk. unfold nZ_of. assert (0 <= k / 100 <= k) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia. Qed.

(* [comment removed for export] *)
Lemma hz_dec_cps : forall (Σ : rts RT) (m : mem) zb ob oc (str j7 : list byte) (s7 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(ob, oc); (zb, nZ_of n)] -> oc = Z.max (2 * n) 1 -> wr_at asegs m ob oc ->
  enc_ok bs (bs_of n) (wf_of n) str -> Z.of_nat (length str) <= nZ_of n -> bytes_at asegs m zb str ->
  rw_cells asegs m (Fr + 32) [C4 (Z_to_bv 64 (Z.of_nat (length str)))] -> rw_cells asegs m (Fr + 48) [C4 (Z_to_bv 64 (2 * n)); CB 4 j7] ->
  rt_credit RT Σ0 - FUZZ_COST + B2BD_COST <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 0x81a7c) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 ob) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 Fr) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb) s7 (Z_to_bv 64 (Fr + 48)) (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 0x81a7c)) fc None m (seg_rom asegs)))) HQc.
Proof using OK AF LIB_loc FRE MCMP B2BD RTW.
  intros Σ m zb ob oc str j7 s7 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S OC OBW ENC DLB ZBB NZC NOC CRX T c Hc Hk.
  pose proof H as (ART0 & MI0 & ST0 & PR0 & _ & _ & _ & SH0). pose proof S as (LV & FRS & SP0).
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST. pose proof (hz_F64 OK) as F64. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FLO OK) as FLO. pose proof (hz_NB OK) as NB. pose proof (nZ_bound n ltac:(lia)) as NZB.
  assert (INZ : In (zb, nZ_of n) (rt_live RT Σ)) by (rewrite LV; right; left; reflexivity).
  assert (INO : In (ob, oc) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m ob oc ART0 INO) as (OB0 & OBH & _). pose proof (af_live_range RT AF Σ m zb (nZ_of n) ART0 INZ) as (ZB0 & ZBH & _).
  rewrite SP0 in OBH, ZBH. pose proof (hz_LOW OK) as LOW. pose proof (hz_SP0R OK) as SP0R.
  assert (NE : ob <> zb).
  { pose proof (af_live_disj RT AF Σ m zb (nZ_of n) ob oc [(ob, oc)] live0 ART0 LV ltac:(left; reflexivity)) as D. lia. }
  (* [comment removed for export] *)
  pose proof (hz_wE usp spa Fr d n zb ob (Z.of_nat (length str)) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 c11 t3 t4 t5 t6 F fc m ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(ul) ltac:(lia) NZC MI0) as W.
  to_cps W c Hc Σ MST. intros cf1 Hc1. destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & -> & Hc1'). clear Hc1.
  set (sm := n mod 2 =? 1).
  assert (ESM : n mod 2 = if sm then 1 else 0) by (unfold sm; destruct (Z.eqb_spec (n mod 2) 1) as [E|E]; [exact E| pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia]).
  rewrite ESM in Hc1'.
  destruct (wr_at_rw_CB m ob (2 * n) (wr_at_sub m ob oc ob (2 * n) OBW ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (junk & OBJ).
  destruct (hz_sh0_parts m (shad Fr) SH0) as (_ & SH6).
  assert (ESH : shad (Fr + 48) = shad Fr + 6) by (unfold shad; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T cf1 _ Hc1' _).
  { eapply (r33 (B2BD Σ PMc) m ob (Fr + 48) zb (2 * n) oc (nZ_of n) str junk sm lo); try reflexivity.
    - exact (hz_FDO OK).
    - exact MST.
    - exact (hz_TP OK).
    - lia.
    - exact DLB.
    - lia.
    - exact ZBB.
    - exact INZ.
    - exact INO.
    - lia.
    - exact NE.
    - exact OBJ.
    - exists Fr, 0%nat. split; [rewrite FRS; left; reflexivity|]. change (fs_size 0) with 64. lia.
    - exact (rw_cells_head m _ _ _ NOC).
    - Z.div_mod_to_equations. lia.
    - rewrite ESH. exact SH6.
    - intros p k Hin. rewrite LV in Hin. destruct Hin as [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia| pose proof (hz_POS OK p k Hin); lia].
    - rewrite LV. cbn [length app]. pose proof (hz_LVB OK). ul.
    - rewrite FRS. cbn. unfold B2B_FRAMES, FRAMES_MAX. lia.
    - pose proof (hz_CRB OK). ul.
    - exact (hm_record OK Σ m H).
    - exact (hm_lib LIB_loc OK Σ m H).
    - exact ART0.
    - exact MI0.
    - rewrite (hz_EU OK). exact ST0.
    - rewrite SP0. exact LOW.
    - rewrite (hz_EU OK). pose proof (hz_LOR OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPT OK). ul.
    - rewrite (hz_EU OK). pose proof (hz_SPA2 OK). Z.div_mod_to_equations. lia.
    - rewrite (hz_EU OK), SP0. pose proof (hz_SPS OK). lia. }
  intros cf2 (Σ1 & rc & dlv & Hc2 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m1 & RS2 & (ART1 & MI1 & ST1) & PR1 & DLC & _ & RES) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->).
  rewrite (hz_EU OK) in ST1, PR1. rewrite FRS in PR1. rewrite LV in PR1 at 1.
  assert (LVI : forall e, In e live0 -> In e ((ob, oc) :: (zb, nZ_of n) :: live0)) by (intros e He; right; right; exact He).
  assert (H1 : HMc Σ1 m1).
  { apply (hm_step OK Σ Σ1 m m1 H ART1 MI1 ST1). apply (core_of_pres_fp OK _ _ m m1 PR1 LVI). intros x Hx. cbn [outside].
    pose proof (core_not_chunk AF OK Σ m _ ob oc ART0 S ltac:(left; reflexivity) x Hx). pose proof (core_not_cells OK x Hx). lia. }
  assert (S1 : HSc Σ1 [(ob, oc); (zb, nZ_of n)]) by (split; [rewrite LV1; exact LV| split; [rewrite FRS1; exact FRS| rewrite SP1; exact SP0]]).
  assert (CRX1 : rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ1) by lia.
  destruct RES as [(-> & out & DEC & DLV & DLVC & OBB)|RCN].
  - (* [comment removed for export] *)
    pose proof (RTW bs (bs_of n) (wf_of n) str sm (2 * n) out ltac:(lia) ENC DEC) as EO. subst out.
    assert (NOC1 : rw_cells asegs m1 (Fr + 48) [C4 (Z_to_bv 64 n); CB 4 j7]).
    { change [C4 (Z_to_bv 64 n); CB 4 j7] with ([C4 (Z_to_bv 64 n)] ++ [CB 4 j7]). apply rw_cells_app. split; [rewrite <- DLV; exact DLC|].
      pose proof (rw_cells_tail m _ _ _ NOC) as TL. cbn [csize cells_size Nat.add] in TL |- *.
      apply (rw_cells_agree_nw asegs m m1 _ _ TL). apply (agree_of_pres_fp _ _ _ _ _ _ _ PR1). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [right; right; right; left; exists Fr, 0%nat; split; [left; reflexivity| change (fs_size 0) with 64; lia]|].
      cbn [outside]. pose proof (hs_chunk_frame AF ART0 S (or_introl eq_refl)) as CF. lia. }
    pose proof (hz_wF usp spa Fr d n zb ob j7 gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c11 w3 w4 w5 w6 F1 fc1 m1 ltac:(lia) ltac:(lia) ltac:(lia) NOC1 MI1) as W.
    to_cps W cf2 Hc2' Σ1 MST. intros cf3 Hc3. destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
    (* [comment removed for export] *)
    assert (INO1 : In (ob, oc) (rt_live RT Σ1)) by (rewrite LV1; exact INO).
    pose proof (hz_DHI OK) as DHI. pose proof (hz_D0 OK) as D0.
    refine (cps_realizes asegs _ _ T cf3 _ Hc3' _).
    { unfold hz_call. eapply (r33 (MCMP Σ1 PMc) m1 d ob bs bs lo); try reflexivity.
      - exact (hz_FDO OK).
      - exact MST.
      - ul.
      - ul.
      - lia.
      - exact (hm_payload OK Σ1 m1 H1).
      - exact OBB.
      - split; [| left; lia]. intros NP. destruct (hz_INP OK) as [E|(IN0 & P0 & P1)]; [rewrite E in NP; cbn in NP; lia|].
        assert (IN1 : In (p0, n0) (rt_live RT Σ1)) by (rewrite LV1, LV; apply LVI; exact IN0).
        split; [apply (acc_sub asegs m1 p0 n0); [exact (proj2 (af_acc_live RT AF Σ1 m1 p0 n0 ART1 IN1))| lia| lia]|].
        left. exists p0, n0. split; [exact IN1| lia].
      - split; [| left; lia]. intros NP.
        split; [apply (acc_sub asegs m1 ob oc); [exact (proj2 (af_acc_live RT AF Σ1 m1 ob oc ART1 INO1))| lia| lia]|].
        left. exists ob, oc. split; [exact INO1| lia].
      - exact ART1.
      - exact MI1.
      - exact (hm_call_ok OK Σ1 m1 _ H1 S1). }
    intros cf4 Hc4. unfold icpt_post in Hc4.
    destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m2 & RS4 & (ART2 & MI2 & _ & ST2) & PR2 & _) & Hc4'). clear Hc4.
    destruct RS4 as (x0 & x1 & x2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & x3 & x4 & x5 & x6 & F2 & fc2 & ->).
    rewrite (hz_EU OK) in ST2, PR2. rewrite FRS1, FRS, LV1, LV in PR2. cbn [app] in PR2. rewrite memcmp_res_refl in Hc4'.
    assert (H2 : HMc Σ1 m2).
    { apply (hm_step OK Σ1 Σ1 m1 m2 H1 ART2 MI2 ST2). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR2). intros x Hx.
      split; [exact (core_client OK _ LVI x Hx)| lia]. }
    pose proof (hz_wG usp spa Fr d n zb ob gp tp x0 x1 x2 f1 f2 f3 f4 f5 f6 f7 c11 x3 x4 x5 x6 F2 fc2 m2 ltac:(ul)) as W.
    to_cps W cf4 Hc4' Σ1 MST. intros cf5 Hc5. destruct (ASTA_unpack RT Σ1 _ _ cf5 Hc5) as (ms5 & <- & Hc5'). clear Hc5.
    exact (hz_free2_cps RT LIB AF LIB_loc FRE Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK Σ1 m2 zb (nZ_of n) ob oc
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 H2 S1 ltac:(lia) ltac:(lia) CRX1 T cf5 Hc5' Hk).
  - (* [comment removed for export] *)
    pose proof (hz_wF_err usp spa Fr d n zb ob rc gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c11 w3 w4 w5 w6 F1 fc1 m1 RCN ltac:(ul)) as W.
    to_cps W cf2 Hc2' Σ1 MST. intros cf3 Hc3. destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
    exact (hz_free2_cps RT LIB AF LIB_loc FRE Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0 d bs p0 n0 spa Fr OK Σ1 m1 zb (nZ_of n) ob oc
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 H1 S1 ltac:(lia) ltac:(lia) CRX1 T cf3 Hc3' Hk).
Qed.

End RoundTrip.
