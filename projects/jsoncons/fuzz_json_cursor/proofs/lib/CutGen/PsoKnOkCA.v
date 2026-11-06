(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCA PsoSemA PsoSemCA PsoKnCA PsoBaseCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSOC.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_casan.

Module PSOKK.

Section G.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Lemma KR : forall Ex (Mv : mem) e v lo hi, CL5A.uv Ex e = v -> lo <= v <= hi -> kentry_ok segs Ex Mv (KRange e lo hi).
Proof. intros Ex Mv e v lo hi Hv Hr. cbn [kentry_ok]. unfold CL5A.uv in Hv. rewrite Hv. exact Hr. Qed.
Lemma KA : forall Ex (Mv : mem) e v m, CL5A.uv Ex e = v -> 0 < m -> v mod m = 0 -> kentry_ok segs Ex Mv (KAlign e m).
Proof. intros Ex Mv e v m Hv Hm Hr. cbn [kentry_ok]. unfold CL5A.uv in Hv. rewrite Hv. split; [exact Hm | exact Hr]. Qed.
Lemma KD : forall Ex (Mv : mem) b1 o1 n1 b2 o2 n2 x1 l1 x2 l2, CL5A.uv Ex b1 = x1 -> CL5A.uv Ex n1 = l1 -> CL5A.uv Ex b2 = x2 -> CL5A.uv Ex n2 = l2 ->
  (x1 + o1 + l1 <= x2 + o2 \/ x2 + o2 + l2 <= x1 + o1) -> kentry_ok segs Ex Mv (KDisj (SA b1 o1) n1 (SA b2 o2) n2).
Proof. intros Ex Mv b1 o1 n1 b2 o2 n2 x1 l1 x2 l2 H1 H2 H3 H4 H. cbn [kentry_ok]. unfold estart, elenZ, CL5A.uv in *. cbn [a_base a_off]. rewrite H1, H2, H3, H4. exact H. Qed.

Lemma KDsh1 : forall Ex (Mv : mem) b1 n1 b2 o2 n2 x1 l1 x2 l2, CL5A.uv Ex b1 = x1 -> CL5A.uv Ex n1 = l1 -> CL5A.uv Ex b2 = x2 -> CL5A.uv Ex n2 = l2 ->
  (x1 / 8 + SB + l1 <= x2 + o2 \/ x2 + o2 + l2 <= x1 / 8 + SB) -> kentry_ok segs Ex Mv (KDisj (SA (EAlu Instr.ALU_SRL b1 (ELit 3)) SBz) n1 (SA b2 o2) n2).
Proof.
  intros Ex Mv b1 n1 b2 o2 n2 x1 l1 x2 l2 H1 H2 H3 H4 H. cbn [kentry_ok]. rewrite CL5A.estart_srl3'. unfold estart, elenZ. cbn [a_base a_off]. unfold CL5A.uv in *.
  rewrite H1, H2, H3, H4. unfold SBz, SB in *. exact H.
Qed.
Lemma KDsh2 : forall Ex (Mv : mem) b1 n1 b2 n2 x1 l1 x2 l2, CL5A.uv Ex b1 = x1 -> CL5A.uv Ex n1 = l1 -> CL5A.uv Ex b2 = x2 -> CL5A.uv Ex n2 = l2 ->
  (x1 / 8 + l1 <= x2 / 8 \/ x2 / 8 + l2 <= x1 / 8) ->
  kentry_ok segs Ex Mv (KDisj (SA (EAlu Instr.ALU_SRL b1 (ELit 3)) SBz) n1 (SA (EAlu Instr.ALU_SRL b2 (ELit 3)) SBz) n2).
Proof.
  intros Ex Mv b1 n1 b2 n2 x1 l1 x2 l2 H1 H2 H3 H4 H. cbn [kentry_ok]. rewrite !CL5A.estart_srl3'. unfold elenZ. unfold CL5A.uv in *.
  rewrite H1, H2, H3, H4. unfold SBz, SB in *. clear - H. lia.
Qed.
Lemma KW64 : forall Ex (H : word -> bool) (Mx : mem) b o v x z, CL5A.uv Ex b = x -> CL5A.uv Ex v = z -> 0 <= x + o -> x + o + 8 <= 2 ^ 64 ->
  CL5A.visr H (x + o) 8 -> L5.u64_at segs Mx (x + o) z -> kentry_ok segs Ex (mrestrict H Mx) (KWord (SA b o) 8 v).
Proof.
  intros Ex H Mx b o v x z Hb Hv R0 R1 VI RD. apply (CL5.kword64_intro segs Ex _ _ v (x + o) z); [unfold estart; cbn [a_base a_off]; unfold CL5A.uv in Hb; rewrite Hb; reflexivity | exact R0 | exact R1 | |].
  - unfold CL5A.uv in Hv. rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned.
  - exact (CL5A.u64_vis segs H Mx (x + o) z R0 R1 VI RD).
Qed.
Lemma KW32 : forall Ex (H : word -> bool) (Mx : mem) b o v x z, CL5A.uv Ex b = x -> CL5A.uv Ex v = z -> 0 <= x + o -> x + o + 4 <= 2 ^ 64 ->
  CL5A.visr H (x + o) 4 -> L5.u32_at segs Mx (x + o) z -> kentry_ok segs Ex (mrestrict H Mx) (KWord (SA b o) 4 v).
Proof.
  intros Ex H Mx b o v x z Hb Hv R0 R1 VI RD. cbn [kentry_ok].
  assert (Hfl : flat Ex (SA b o) (Z.of_nat 4)) by (unfold flat, estart; cbn [a_base a_off]; unfold CL5A.uv in Hb; rewrite Hb; clear - R0 R1; lia).
  split; [clear; lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start Ex _ _ Hfl). unfold estart. cbn [a_base a_off]. unfold CL5A.uv in Hb, Hv. rewrite Hb.
  rewrite <- (Z_to_bv_bv_unsigned _ (edenot Ex v)), Hv. exact (CL5A.u32_vis segs H Mx (x + o) z R0 R1 VI RD).
Qed.
Lemma KW8 : forall Ex (H : word -> bool) (Mx : mem) b o v x z, CL5A.uv Ex b = x -> CL5A.uv Ex v = z -> 0 <= x + o -> x + o + 1 <= 2 ^ 64 ->
  CL5A.visr H (x + o) 1 -> L5.u8_at segs Mx (x + o) z -> kentry_ok segs Ex (mrestrict H Mx) (KWord (SA b o) 1 v).
Proof.
  intros Ex H Mx b o v x z Hb Hv R0 R1 VI RD. pose proof (CL5A.uv_range Ex v) as VR. rewrite Hv in VR.
  apply (CL5A.kword8_intro segs Ex _ _ v (x + o) z); [unfold estart; cbn [a_base a_off]; unfold CL5A.uv in Hb; rewrite Hb; reflexivity | exact R0 | exact R1 | | exact VR |].
  - unfold CL5A.uv in Hv. rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned.
  - exact (CL5A.u8_vis segs H Mx (x + o) z R0 R1 VI RD).
Qed.
Lemma KU : forall Ex (H : word -> bool) (Mx : mem) b o n x l, CL5A.uv Ex b = x -> CL5A.uv Ex n = l -> 0 <= x + o -> x + o + l <= 2 ^ 64 -> x + o < 2 ^ 64 ->
  CL5A.visr H (x + o) l -> L5.defined Mx (x + o) l -> kentry_ok segs Ex (mrestrict H Mx) (KUnk (SA b o) n).
Proof.
  intros Ex H Mx b o n x l Hb Hn R0 R1 R2 VI DF. apply (CL5.kunk_intro segs Ex _ _ n (x + o) l); [unfold estart; cbn [a_base a_off]; unfold CL5A.uv in Hb; rewrite Hb; reflexivity | exact Hn | exact R0 | exact R1 | exact R2 |].
  exact (CL5A.defined_vis H Mx (x + o) l VI DF).
Qed.
Lemma KWR : forall Ex (H : word -> bool) (Mx : mem) b o n x l, CL5A.uv Ex b = x -> CL5A.uv Ex n = l -> 0 <= x + o -> x + o + l <= 2 ^ 64 -> x + o < 2 ^ 64 ->
  CL5A.visr H (x + o) l -> L5.defined Mx (x + o) l -> kentry_ok segs Ex (mrestrict H Mx) (KWr (SA b o) n).
Proof.
  intros Ex H Mx b o n x l Hb Hn R0 R1 R2 VI DF. apply (CL5.kwr_intro segs Ex _ _ n (x + o) l); [unfold estart; cbn [a_base a_off]; unfold CL5A.uv in Hb; rewrite Hb; reflexivity | exact Hn | exact R0 | exact R1 | exact R2 |].
  exact (CL5A.defined_vis H Mx (x + o) l VI DF).
Qed.

Lemma KZsh : forall Ex (H : word -> bool) (Mx : mem) pe ne p g, CL5A.uv Ex pe = p -> CL5A.uv Ex ne = g -> 0 <= g < 2 ^ 40 -> 0 <= p < 2 ^ 47 ->
  (forall j, 0 <= j < g -> H (Z_to_bv 64 (S p + j)) = false) -> shadow_zero Mx p g -> kentry_ok segs Ex (mrestrict H Mx) (KZero (SA (EAlu Instr.ALU_SRL pe (ELit 3)) SBz) ne).
Proof.
  intros Ex H Mx pe ne p g Hp Hg Rg Rp VI HZ. assert (Hd : 0 <= p / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply (CL5A.kzero_intro segs Ex _ _ ne (p / 8 + SB) g); [rewrite CL5A.estart_srl3', Hp; reflexivity | exact Hg | unfold SB; lia | unfold SB; lia | unfold SB; lia |].
  intros j Hj. replace (p / 8 + SB + j) with (S p + j) by (unfold S; lia). apply CL5A.byte_vis; [exact (VI j Hj) | exact (HZ j Hj)].
Qed.

Lemma u8_mod : forall (Mx : mem) a v, L5.u8_at segs Mx a v -> L5.u8_at segs Mx a (v mod 256).
Proof.
  intros Mx a v Hu. unfold L5.u8_at in *. rewrite Hu. do 2 f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_modulus 8) with 256.
  unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma sw_level : forall psx w, PML.ps_level (PML.ps_set_win psx w) = PML.ps_level psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_st : forall psx w, PML.ps_st (PML.ps_set_win psx w) = PML.ps_st psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_sst : forall psx w, PML.ps_sst (PML.ps_set_win psx w) = PML.ps_sst psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_nst : forall psx w, PML.ps_nst (PML.ps_set_win psx w) = PML.ps_nst psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_more : forall psx w, PML.ps_more (PML.ps_set_win psx w) = PML.ps_more psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_done : forall psx w, PML.ps_done (PML.ps_set_win psx w) = PML.ps_done psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_stack : forall psx w, PML.ps_stack (PML.ps_set_win psx w) = PML.ps_stack psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_sb : forall psx w, PML.ps_sb (PML.ps_set_win psx w) = PML.ps_sb psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_scap : forall psx w, PML.ps_scap (PML.ps_set_win psx w) = PML.ps_scap psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_bcap : forall psx w, PML.ps_bcap (PML.ps_set_win psx w) = PML.ps_bcap psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_bptr : forall psx w, PML.ps_bptr (PML.ps_set_win psx w) = PML.ps_bptr psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_buf : forall psx w, PML.ps_buf (PML.ps_set_win psx w) = PML.ps_buf psx. Proof. intros [] w; reflexivity. Qed.
Lemma sw_win : forall psx w, PML.ps_win (PML.ps_set_win psx w) = w. Proof. intros [] w; reflexivity. Qed.

Lemma DIV8K : forall a k, a mod 8 = 0 -> (a + k) / 8 = a / 8 + k / 8.
Proof.
  intros a k Ha. rewrite (Z_div_mod_eq_full a 8) at 1. rewrite Ha, Z.add_0_r, Z.mul_comm. rewrite Z.div_add_l by (clear; lia). reflexivity.
Qed.
Lemma SHD1 : forall a n b, a mod 8 = 0 -> b mod 8 = 0 -> 0 <= n -> a + n <= b -> a / 8 + (n + 7) / 8 <= b / 8.
Proof.
  intros a n b Ha Hb N0 H. pose proof (Z_div_mod_eq_full a 8) as DA. pose proof (Z_div_mod_eq_full b 8) as DB. rewrite Ha, Z.add_0_r in DA. rewrite Hb, Z.add_0_r in DB.
  assert (X : (n + 7) / 8 < b / 8 - a / 8 + 1) by (apply Z.div_lt_upper_bound; clear - DA DB H; lia). clear - X. lia.
Qed.
Lemma SHD : forall a n b m, a mod 8 = 0 -> b mod 8 = 0 -> 0 <= n -> 0 <= m -> (a + n <= b \/ b + m <= a) -> a / 8 + (n + 7) / 8 <= b / 8 \/ b / 8 + (m + 7) / 8 <= a / 8.
Proof. intros a n b m Ha Hb N0 M0 [H|H]; [left; exact (SHD1 a n b Ha Hb N0 H) | right; exact (SHD1 b m a Hb Ha M0 H)]. Qed.

Lemma WINC : forall (Mx : mem) P0 w,
  match w with None => PMLA.u64 segs Mx (P0 + 192) 0 /\ PMLA.u64 segs Mx (P0 + 200) 0 | Some (p, e) => PMLA.u64 segs Mx (P0 + 200) p /\ PMLA.u64 segs Mx (P0 + 192) e /\ p <= e end ->
  L5.u64_at segs Mx (P0 + 192) (PSOI.whi w) /\ L5.u64_at segs Mx (P0 + 200) (PSOI.wlo w).
Proof. intros Mx P0 [[p0 e0]|] CW; cbn [PSOI.whi PSOI.wlo]; [destruct CW as (X1 & X2 & _); split; [exact X2 | exact X1] | exact CW]. Qed.
End G.

Section K.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).
Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation LAY := (PSOI.iLAY I).
Local Abbreviation ch := (PSOI.ich I).   Local Abbreviation wp0 := (PSOI.wp0 I).  Local Abbreviation we0 := (PSOI.we0 I). Local Abbreviation wlen := (PSOI.wlen I). Local Abbreviation chg := (PSOI.chg I).

Variables (Ex : env) (Mx : mem) (Ax : list (Z * Z)) (mx : Model) (FFx LKx : list fframe) (crx : credit) (ps1 : PML.pstate) (mw : option (Z * Z)).
Variables (bp bc sbp sc : Z).
Variables (xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap : expr).

Record knh : Prop := KNH {
  kB1 : PML.ps_bptr ps1 = bp;  kB2 : PML.ps_bcap ps1 = bc;  kB3 : PML.ps_sb ps1 = sbp;  kB4 : PML.ps_scap ps1 = sc;
  kHH : ri_inv HI ([(bp, bc); (sbp, sc)] ++ LBo) FFx LKx crx Ax Mx (vml_of mx);
  kFF : incl FF FFx;
  kPA : PMLA.parser_at (hl_segs L) IC Mx P (PML.ps_set_win ps1 mw);
  kSH : PMLA.parser_sh Mx ps1;
  kWF : PML.wf_ps ps1;
  kBC : bc <= 2 ^ 27;
  kSZ : Z.of_nat (length (PML.ps_buf ps1)) < 2 ^ 26;

  kV10 : CL5A.uv Ex (EVar 10) = P;  kV11 : CL5A.uv Ex (EVar 11) = V;  kV12 : CL5A.uv Ex (EVar 12) = E;  kV2 : CL5A.uv Ex (EVar 2) = sp;
  kV32 : CL5A.uv Ex (EVar 32) = wlen;  kV34 : CL5A.uv Ex (EVar 34) = ch;  kV35 : CL5A.uv Ex (EVar 35) = chg;  kV36 : CL5A.uv Ex (EVar 36) = wp0;

  kXLV : CL5A.uv Ex xlevel = PML.ps_level ps1 mod 2 ^ 32;
  kXWE : CL5A.uv Ex xwend = PSOI.whi mw;
  kXWP : CL5A.uv Ex xwptr = PSOI.wlo mw;
  kXST : CL5A.uv Ex xst = PML.ps_st ps1 mod 256;
  kXSST : CL5A.uv Ex xsst = PML.ps_sst ps1;
  kXNST : CL5A.uv Ex xnst = PML.ps_nst ps1;
  kXMORE : CL5A.uv Ex xmore = PML.b2z (PML.ps_more ps1);
  kXDONE : CL5A.uv Ex xdone = PML.b2z (PML.ps_done ps1);
  kXK : CL5A.uv Ex xk = bc / 2;
  kXSIZE : CL5A.uv Ex xsize = Z.of_nat (length (PML.ps_buf ps1));
  kXP : CL5A.uv Ex xp = bp;
  kXSB : CL5A.uv Ex xsb = sbp;
  kXSLEN : CL5A.uv Ex xslen = Z.of_nat (length (PML.ps_stack ps1));
  kXSCAP : CL5A.uv Ex xscap = sc }.

Record knf : Prop := KNF {
  kF : ar_fs ar <= CL5A.uv Ex (EVar 65) /\ CL5A.uv Ex (EVar 65) + 1024 <= ar_fs ar + 11571200 /\ CL5A.uv Ex (EVar 65) mod 64 = 0;
  kFL : ar_fs ar <= CL5A.uv Ex (EVar 60) < ar_fs ar + 11571200 }.
Hypothesis KH : knh.

Let HB4 : PML.ps_bptr ps1 = bp /\ PML.ps_bcap ps1 = bc /\ PML.ps_sb ps1 = sbp /\ PML.ps_scap ps1 = sc := conj (kB1 KH) (conj (kB2 KH) (conj (kB3 KH) (kB4 KH))).
Let HHx := kHH KH.  Let HFF := kFF KH.  Let PA := kPA KH.  Let SH := kSH KH.  Let WF := kWF KH.  Let HBC := kBC KH.  Let HSZ := kSZ KH.
Let V10 := kV10 KH.  Let V11 := kV11 KH.  Let V12 := kV12 KH.  Let V2 := kV2 KH.  Let V32 := kV32 KH.  Let V34 := kV34 KH.  Let V35 := kV35 KH.  Let V36 := kV36 KH.
Let XLV := kXLV KH.  Let XWE := kXWE KH.  Let XWP := kXWP KH.  Let XST := kXST KH.  Let XSST := kXSST KH.  Let XNST := kXNST KH.  Let XMORE := kXMORE KH.
Let XDONE := kXDONE KH.  Let XK := kXK KH.  Let XSIZE := kXSIZE KH.  Let XP := kXP KH.  Let XSB := kXSB KH.  Let XSLEN := kXSLEN KH.  Let XSCAP := kXSCAP KH.

Let Hv := ahid Ax mx.
Let segs := hl_segs L.
Let LBx := [(bp, bc); (sbp, sc)] ++ LBo.

Record facts : Prop := FACTS {
  f_P : 0 <= P /\ P + 272 <= 2 ^ 47 /\ P mod 8 = 0 /\ ar_fs ar + 32 <= P /\ P + 272 + 8 <= ar_fs ar + FS_BYTES /\ (P + 272 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= P) /\ P + 272 <= ahl_ceil ar;
  f_V : 0 <= V /\ V + 48 <= 2 ^ 47 /\ V mod 8 = 0 /\ ar_fs ar + 32 <= V /\ V + 48 + 8 <= ar_fs ar + FS_BYTES /\ (V + 48 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= V);
  f_E : 0 <= E /\ E + 16 <= 2 ^ 47 /\ E mod 8 = 0 /\ ar_fs ar + 32 <= E /\ E + 16 + 8 <= ar_fs ar + FS_BYTES /\ (E + 16 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= E);
  f_fs : 7024640 <= ar_fs ar /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ 0x7fff7f800000 <= ahl_ceil ar /\ ahl_ceil ar + 4096 + 10496 <= sp /\ sp <= ar_sptop ar /\ ar_sptop ar <= 2 ^ 47 /\ sp mod 32 = 0;
  f_B : 4096 <= bp /\ bp + bc <= ahl_ceil ar /\ bp mod 16 = 0 /\ 264 <= bc <= 2 ^ 27 /\ bc mod 8 = 0 /\ (bp + bc <= BIGSHADOW_LO \/ BIGSHADOW_HI <= bp) /\ (bp + bc <= hl_img_lo L \/ hl_img_hi L <= bp)
        /\ (bp + bc <= ar_fs ar \/ ar_fs ar + FS_BYTES <= bp) /\ Z.of_nat (length (PML.ps_buf ps1)) < bc /\ L5.defined Mx bp bc;
  f_S : 4096 <= sbp /\ sbp + sc <= ahl_ceil ar /\ sbp mod 16 = 0 /\ 66 <= sc <= 1056 /\ (sbp + sc <= BIGSHADOW_LO \/ BIGSHADOW_HI <= sbp) /\ (sbp + sc <= hl_img_lo L \/ hl_img_hi L <= sbp)
        /\ (sbp + sc <= ar_fs ar \/ ar_fs ar + FS_BYTES <= sbp) /\ 1 <= Z.of_nat (length (PML.ps_stack ps1)) <= 1027 /\ Z.of_nat (length (PML.ps_stack ps1)) <= sc /\ L5.defined Mx sbp sc /\ In sc [66; 132; 264; 528; 1056];
  f_BS : bp + bc <= sbp \/ sbp + sc <= bp;
  f_W : 0 <= wp0 /\ 0 <= wlen <= 16384 /\ 0 <= ch /\ ch + 16384 <= 2 ^ 47 /\ 0 <= chg <= 2048 /\
        ((wp0 = 0 /\ wlen = 0 /\ chg = 0 /\ ch = 0) \/ (ch <= wp0 /\ wp0 + wlen <= ch + 16384 /\ chg = 2048 /\ ch mod 16 = 0 /\ (bp + bc <= ch \/ ch + 16384 <= bp) /\ (sbp + sc <= ch \/ ch + 16384 <= sbp)));
  f_ps : 0 <= PML.ps_sst ps1 <= 11 /\ 0 <= PML.ps_nst ps1 <= 7;
  f_img : hl_img_lo L = 65536 /\ hl_img_hi L = 7024640 }.

Lemma FX : facts.
Proof.
  pose_facts I.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) as WFx. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFx) as RGx.
  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHx) as [WBx _].
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFx (bp, bc) (or_introl eq_refl)) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & Ddef & _ & Dbap & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7, Ddef, Dbap.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFx (sbp, sc) (or_intror (or_introl eq_refl))) as ((G0 & G1 & G16 & G3 & G4 & (G5 & G6 & G7)) & Gdef & _ & Gbap & _). cbn [fst snd] in G0, G1, G16, G3, G4, G5, G6, G7, Gdef, Gbap.
  destruct (WBx (bp, bc) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & _ & D9). cbn [fst snd] in D9.
  destruct (WBx (sbp, sc) (or_intror (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & G9). cbn [fst snd] in G9.
  pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ WFx) as [ND _]. cbn [map fst app] in ND.
  destruct HB4 as (HB1 & HB2 & HB3 & HB4').
  pose proof (PTB.pa_buf L IC Mx P _ PA) as STR. pose proof (PTB.pa_bcap L IC Mx P _ PA) as BC264. pose proof (PTB.pa_slen L IC Mx P _ PA) as SL.
  rewrite sw_bcap, sw_bptr, sw_buf, HB1, HB2 in STR. rewrite sw_bcap, HB2 in BC264. rewrite sw_stack, sw_scap, HB4' in SL.
  destruct STR as ((_ & _ & _ & _ & _ & _) & BC8x & SLT).
  pose proof (PSSA.wf_shape _ WF) as (W1 & W2 & W3 & W4). rewrite HB4' in W4.
  assert (SCR' : 66 <= sc <= 1056) by (cbn [In] in W4; clear - W4; lia).
  assert (BS : bp + bc <= sbp \/ sbp + sc <= bp).
  { specialize (Dbap (sbp, sc)). cbn [fst snd lb_remove app] in Dbap. rewrite Z.eqb_refl in Dbap. specialize (Dbap (or_introl eq_refl)). clear - Dbap. lia. }
  destruct (CHA.rf_fs _ _ _ _ RFx) as ((FQ0 & FQ1 & FQ2) & FQ3 & _).
  constructor.
  - unfold FS_BYTES in *. clear - O1 O2 O3 O4 O5 O6 P8. unfold hid in *. unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
  - unfold FS_BYTES in *. clear - VR1 VR2 VR3 VR4 VR5 VR6 V8. unfold hid in *. unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
  - unfold FS_BYTES in *. clear - Q1 Q2 Q3 Q4 Q5 Q6 E8. unfold hid in *. unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
  - pose proof (PSOI.iHsp32 I) as Hsp32. clear - FSLO FQ3 CL S2 S3 SP1 Hsp32. unfold PSOC.SCR in *. lia.
  - split; [exact D0|]. split; [exact D4|]. split; [exact D16|]. split; [clear - BC264 HBC; lia|].
    split; [exact BC8x|]. split; [exact D6|]. split; [exact D1|]. split; [clear - D9; unfold FS_BYTES in *; lia|]. split; [exact SLT | exact Ddef].
  - split; [exact G0|]. split; [exact G4|]. split; [exact G16|]. split; [exact SCR'|]. split; [exact G6|]. split; [exact G1|]. split; [clear - G9; unfold FS_BYTES in *; lia|].
    split; [clear - W3; lia|]. split; [exact SL|]. split; [exact Gdef | exact W4].
  - exact BS.
  - split; [exact WI0|]. split; [exact WI2|]. split; [exact WI3|]. split; [exact WI4|]. split; [exact WI5|].
    destruct WIC as [Hw|(INC & C1 & C2 & C3 & C16)].
    + left. pose proof (PSOI.WNONE I Hw) as (X0 & _ & X2 & X3 & X4). exact (conj X0 (conj X2 (conj X3 X4))).
    + right. split; [exact C1|]. split; [clear - C2 WI6; lia|]. split; [exact C3|]. split; [exact C16|].
      assert (INCo : In (ch, 16384) LBo).
      { destruct (PSOI.win I) as [[p0 e0]|] eqn:Hw; [exact (proj1 (proj2 (proj2 (proj2 (PSOI.WSOME I p0 e0 Hw)))))|].
        exfalso. pose proof (PSOI.WNONE I Hw) as (_ & _ & _ & X3 & _). clear - X3 C3. lia. }
      split.
      * specialize (Dbap (ch, 16384)). cbn [fst snd lb_remove app] in Dbap. rewrite Z.eqb_refl in Dbap. specialize (Dbap (or_intror INCo)). clear - Dbap. lia.
      * specialize (Gbap (ch, 16384)). cbn [fst snd lb_remove app] in Gbap. rewrite Z.eqb_refl in Gbap.
        specialize (Gbap ltac:(destruct (bp =? sbp); right; exact INCo)). clear - Gbap. lia.
  - split; [exact W1 | exact W2].
  - split; [exact ILO | exact IHI].
Qed.

Lemma UK2 : CL5A.uv Ex (APC.escale 2 xk) = bc.
Proof.
  destruct FX as [_ _ _ _ FB _ _ _ _ _]. rewrite UV_escale2, XK. pose proof (Z_div_mod_eq_full bc 8) as D8. destruct FB as (B0 & B1 & _ & B3 & B8 & _).
  rewrite B8 in D8. replace (2 * (bc / 2)) with bc; [apply Z.mod_small; clear - B0 B1 B3; lia|].
  rewrite D8 at 2. replace (8 * (bc / 8) + 0) with ((4 * (bc / 8)) * 2) by (clear; lia). rewrite Z_div_mult by (clear; lia). clear - D8. lia.
Qed.
Lemma UCAP : CL5A.uv Ex (APC.eaddz (APC.escale 2 xk) 1) = bc + 1.
Proof. destruct FX as [_ _ _ _ FB _ _ _ _ _]. rewrite uv_eaddz, UK2. apply Z.mod_small. clear - FB. lia. Qed.
Lemma UKM1 : CL5A.uv Ex (APC.esub (APC.eaddz (APC.escale 2 xk) (-1)) xsize) = bc - 1 - Z.of_nat (length (PML.ps_buf ps1)).
Proof. destruct FX as [_ _ _ _ FB _ _ _ _ _]. rewrite uv_esub, uv_eaddz, UK2, XSIZE. rewrite (Z.mod_small (bc + -1)) by (clear - FB; lia). apply Z.mod_small. clear - FB. lia. Qed.
Lemma USZP : CL5A.uv Ex (APC.eadd xsize xp) = bp + Z.of_nat (length (PML.ps_buf ps1)).
Proof. destruct FX as [_ _ _ FS FB _ _ _ _ _]. rewrite uv_eadd, XSIZE, XP. rewrite Z.add_comm. apply Z.mod_small. clear - FB FS. lia. Qed.
Lemma USLEN : CL5A.uv Ex (APC.eadd xsb xslen) = sbp + Z.of_nat (length (PML.ps_stack ps1)).
Proof. destruct FX as [_ _ _ FS _ FSt _ _ _ _]. rewrite uv_eadd, XSB, XSLEN. apply Z.mod_small. clear - FSt FS. lia. Qed.
Lemma USCAP : CL5A.uv Ex (APC.eadd xsb xscap) = sbp + sc.
Proof. destruct FX as [_ _ _ FS _ FSt _ _ _ _]. rewrite uv_eadd, XSB, XSCAP. apply Z.mod_small. clear - FSt FS. lia. Qed.
Lemma USCL : CL5A.uv Ex (APC.esub xscap xslen) = sc - Z.of_nat (length (PML.ps_stack ps1)).
Proof. destruct FX as [_ _ _ FS _ FSt _ _ _ _]. rewrite uv_esub, XSCAP, XSLEN. apply Z.mod_small. clear - FSt FS. lia. Qed.
Lemma USC7 : CL5A.uv Ex (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) = (sc + 7) / 8.
Proof.
  destruct FX as [_ _ _ FS _ FSt _ _ _ _]. pose proof (CL5A.elen_srl3' Ex (APC.eaddz xscap 7)) as X. unfold elenZ in X. unfold CL5A.uv at 1. rewrite X.
  rewrite uv_eaddz, XSCAP. rewrite Z.mod_small by (clear - FSt; lia). reflexivity.
Qed.
Lemma UPK : forall k, 0 <= k <= 272 -> CL5A.uv Ex (APC.eaddz (EVar 10) k) = P + k.
Proof. intros k Hk. destruct FX as [FP _ _ _ _ _ _ _ _ _]. rewrite uv_eaddz, V10. apply Z.mod_small. clear - FP Hk. lia. Qed.

Lemma VIS : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FFx sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> Hv (Z_to_bv 64 a) = false.
Proof. intros a Ha Hc Hs. exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ mx sp 0 a HHx Ha Hc Hs). Qed.
Lemma RGX : CHA.rng_facts L ar LBx FFx.
Proof. exact (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx)). Qed.
Lemma VISFR : forall o n a, CL5A.ainfr FF o n -> o <= a < o + n -> 0 <= o -> o + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= o -> o + n <= 2 ^ 47 -> Hv (Z_to_bv 64 a) = false.
Proof.
  intros o n a (f & Hf & F1 & F2) Ha R0 R1 R2. apply VIS; [clear - Ha R0 R2; lia | | apply (CL5A.not_stk_shadow_app L ar LBx FFx a RGX); clear - Ha R1; lia].
  right; right; right; left. exists f. split; [exact (HFF f Hf)|]. clear - F1 F2 Ha. lia.
Qed.
Lemma VISP : forall k n, 0 <= k -> k + n <= 272 -> CL5A.visr Hv (P + k) n.
Proof. intros k n Hk Hn i Hi. destruct FX as [FP _ _ _ _ _ _ _ _ _]. pose proof (PSOI.iOP I) as (Pfr & _). apply (VISFR P 272 _ Pfr); clear - FP Hk Hn Hi; lia. Qed.
Lemma VISE : forall k n, 0 <= k -> k + n <= 16 -> CL5A.visr Hv (E + k) n.
Proof. intros k n Hk Hn i Hi. destruct FX as [_ _ FE _ _ _ _ _ _ _]. pose proof (PSOI.iOE I) as (Efr & _). apply (VISFR E 16 _ Efr); clear - FE Hk Hn Hi; lia. Qed.
Lemma VISV : CL5A.visr Hv V 8.
Proof. intros i Hi. destruct FX as [_ FV _ _ _ _ _ _ _ _]. pose proof (PSOI.iOV I) as (Vfr & _). apply (VISFR V 48 _ Vfr); clear - FV Hi; lia. Qed.
Lemma VISV48 : CL5A.visr Hv V 48.
Proof. intros i Hi. destruct FX as [_ FV _ _ _ _ _ _ _ _]. pose proof (PSOI.iOV I) as (Vfr & _). apply (VISFR V 48 _ Vfr); clear - FV Hi; lia. Qed.
Lemma VISB : forall u n, In (u, n) LBx -> CL5A.visr Hv u n.
Proof.
  intros u n Hun i Hi. destruct (CHA.rf_blk _ _ _ _ RGX (u, n) Hun) as (D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
  apply VIS; [clear - Hi D5 D7; lia | left; exists (u, n); split; [exact Hun | cbn [fst snd]; clear - Hi; lia] | apply (CL5A.not_stk_shadow_app L ar LBx FFx _ RGX); clear - Hi D6; lia].
Qed.
Lemma VISBS : forall u n a, In (u, n) LBx -> in_shadow_of u n a -> Hv (Z_to_bv 64 a) = false.
Proof.
  intros u n a Hun Ha. destruct (CHA.rf_blk _ _ _ _ RGX (u, n) Hun) as (D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
  pose proof (CHA.shadow_range u n a D5 D3 D7 Ha) as RG.
  apply VIS; [clear - RG; lia | do 6 right; exists (u, n); split; [exact Hun | exact Ha] | exact (CL5A.not_stk_shadow_sh L ar LBx FFx u n a RGX D5 D3 D4 Ha)].
Qed.

Lemma PCONST_ok : Forall (kentry_ok segs Ex (CCA.vis Ax mx Mx)) PSOK.PCONST.
Proof.
  destruct FX as [FP _ _ _ _ _ _ _ _ _]. pose proof PA as H. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in H.
  destruct H as (C0 & C8 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & S24 & S48 & S72 & C96 & C128 & _ & _ & _ & _ & _ & _ & _ & C213 & C216 & _).
  destruct S24 as (_ & C24 & _). destruct S48 as (_ & C48 & _). destruct S72 as (_ & C72 & _). cbn [length Z.of_nat Z.mul] in C24, C48, C72.
  assert (UL : forall z, 0 <= z < 2 ^ 64 -> CL5A.uv Ex (ELit z) = z) by (intros z Hz; exact (uv_lit Ex z Hz)).
  unfold PSOK.PCONST, CCA.vis. fold Hv.
  repeat (apply Forall_cons;
    [first [ eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | first [apply UL; clear; lia | apply UPK; clear; lia] | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | rewrite ?Z.add_0_r; assumption]
           | eapply (KW32 segs Ex Hv Mx (EVar 10)); [exact V10 | apply UL; clear; lia | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | assumption]
           | eapply (KW8 segs Ex Hv Mx (EVar 10)); [exact V10 | apply UL; clear; lia | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | assumption] ] |]).
  apply Forall_nil.
Qed.

Lemma PSTATE_ok : Forall (kentry_ok segs Ex (CCA.vis Ax mx Mx)) (PSOK.PSTATE xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap).
Proof.
  destruct FX as [FP _ _ FS FB FSt _ _ Fps _]. destruct HB4 as (HB1 & HB2 & HB3 & HB4').
  pose proof (PTB.pa_level L IC Mx P _ PA) as C144. pose proof (PTB.pa_win L IC Mx P _ PA) as CW. pose proof (PTB.pa_st L IC Mx P _ PA) as C208. pose proof (PTB.pa_sst L IC Mx P _ PA) as C209.
  pose proof (PTB.pa_nst L IC Mx P _ PA) as C210. pose proof (PTB.pa_more L IC Mx P _ PA) as C211. pose proof (PTB.pa_done L IC Mx P _ PA) as C212. pose proof (PTB.pa_buf L IC Mx P _ PA) as STR.
  pose proof (PTB.pa_sb L IC Mx P _ PA) as C248. pose proof (PTB.pa_send L IC Mx P _ PA) as C256. pose proof (PTB.pa_scap L IC Mx P _ PA) as C264. pose proof (PTB.pa_def L IC Mx P _ PA) as PDEF.
  rewrite sw_level in C144. rewrite sw_win in CW. rewrite sw_st in C208. rewrite sw_sst in C209. rewrite sw_nst in C210. rewrite sw_more in C211. rewrite sw_done in C212.
  rewrite sw_bcap, sw_bptr, sw_buf, HB1, HB2 in STR. rewrite sw_sb, HB3 in C248. rewrite sw_sb, sw_stack, HB3 in C256. rewrite sw_sb, sw_scap, HB3, HB4' in C264.
  destruct STR as ((_ & C224 & C232 & C240 & _ & _) & _ & _). replace (P + 224 + 8) with (P + 232) in C232 by (clear; lia). replace (P + 224 + 16) with (P + 240) in C240 by (clear; lia).
  apply (u32_mod I) in C144. apply (u8_mod segs) in C208.
  assert (C192 : L5.u64_at segs Mx (P + 192) (PSOI.whi mw) /\ L5.u64_at segs Mx (P + 200) (PSOI.wlo mw)).
  { exact (WINC segs Mx P mw CW). }
  destruct C192 as [C192 C200].
  unfold PSOK.PSTATE, CCA.vis. fold Hv.
  apply Forall_cons; [eapply (KW32 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XLV | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C144]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XWE | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C192]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XWP | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C200]|].
  apply Forall_cons; [eapply (KW8 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XST | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C208]|].
  apply Forall_cons; [eapply (KW8 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XSST | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C209]|].
  apply Forall_cons; [eapply (KW8 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XNST | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C210]|].
  apply Forall_cons; [eapply (KW8 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XMORE | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C211]|].
  apply Forall_cons; [eapply (KW8 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XDONE | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C212]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact UCAP | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C224]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XSIZE | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C232]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XP | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C240]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact XSB | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C248]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact USLEN | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C256]|].
  apply Forall_cons; [eapply (KW64 segs Ex Hv Mx (EVar 10)); [exact V10 | exact USCAP | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia | exact C264]|].
  apply Forall_cons; [eapply (KU segs Ex Hv Mx (EVar 10)); [exact V10 | apply uv_lit; clear; lia | clear - FP; lia | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia
                                                        | intros i Hi; replace (P + 148 + i) with (P + (148 + i)) by (clear; lia); apply PDEF; clear - Hi; lia]|].
  apply Forall_cons; [eapply (KU segs Ex Hv Mx (EVar 10)); [exact V10 | apply uv_lit; clear; lia | clear - FP; lia | clear - FP; lia | clear - FP; lia | apply VISP; clear; lia
                                                        | intros i Hi; replace (P + 220 + i) with (P + (220 + i)) by (clear; lia); apply PDEF; clear - Hi; lia]|].
  apply Forall_nil.
Qed.

Hypothesis KF : knf.
Lemma SHS : forall o n, o mod 8 = 0 -> 0 <= n -> o + n <= sbp \/ sbp + sc <= o -> o / 8 + (n + 7) / 8 <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= o / 8.
Proof.
  intros o n Ho N0 H. destruct FX as [_ _ _ _ _ FSt _ _ _ _]. destruct FSt as (S0 & _ & S16 & (S2 & _) & _).
  apply (SHD o n sbp sc Ho (CHA.mod8_of_16 _ S16) N0 ltac:(clear - S2; lia) H).
Qed.
Lemma SHB : forall o n, o mod 8 = 0 -> 0 <= n -> o + n <= bp \/ bp + bc <= o -> o / 8 + (n + 7) / 8 <= bp / 8 \/ bp / 8 + (bc + 7) / 8 <= o / 8.
Proof.
  intros o n Ho N0 H. destruct FX as [_ _ _ _ FB _ _ _ _ _]. destruct FB as (B0 & _ & B16 & (B2 & _) & _).
  apply (SHD o n bp bc Ho (CHA.mod8_of_16 _ B16) N0 ltac:(clear - B2; lia) H).
Qed.

Lemma BLOCKS_KN0_ok : Forall (kentry_ok segs Ex (CCA.vis Ax mx Mx)) (PSOK.BLOCKS_KN0 xk xsize xp xsb xslen xscap xlevel).
Proof.
  pose proof FX as FXX. destruct FXX as [FP FV FE FS FB FSt FBS FW Fps Fimg].
  destruct FP as (P0 & P1 & P8 & P2 & P3 & P4 & P5). destruct FV as (V0 & V1' & V8 & V2' & V3 & V4). destruct FE as (E0' & E1 & E8 & E2 & E3 & E4).
  destruct FS as (FS0 & FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
  destruct FB as (B0 & B1 & B16 & (B2 & B3) & B8 & BBS & BIMG & BFS & BSZ & BDEF).
  destruct FSt as (S0 & S1 & S16 & (S2 & S3) & SBS & SIMG & SFS & (SL1 & SL2) & SL3 & SDEF & SIN).
  destruct FW as (W0 & (W1 & W2) & W3 & W4 & (W5 & W6) & WC).
  destruct Fimg as (IM1 & IM2). rewrite IM1, IM2 in BIMG, SIMG.
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  pose proof HSZ as SZ. pose proof UK2 as U2K. pose proof UKM1 as UKM. pose proof USZP as USZ. pose proof USCL as USL. pose proof USC7 as US7.
  pose proof (CHA.mod8_of_16 _ B16) as B8'. pose proof (CHA.mod8_of_16 _ S16) as S8'.
  assert (UL : forall z, 0 <= z < 2 ^ 64 -> CL5A.uv Ex (ELit z) = z) by (intros z Hz; exact (uv_lit Ex z Hz)).
  assert (INB : In (bp, bc) LBx) by (left; reflexivity). assert (INS : In (sbp, sc) LBx) by (right; left; reflexivity).

  pose proof (PTB.pa_buf L IC Mx P _ PA) as STR. destruct HB4 as (HB1 & HB2 & HB3 & HB4').
  rewrite sw_bcap, sw_bptr, sw_buf, HB1, HB2 in STR. destruct STR as ((_ & _ & _ & _ & _ & NUL) & _ & _).
  pose proof SH as (SHB0 & _). unfold PMLA.parser_sh in SHB0. rewrite HB1, HB2 in SHB0. destruct SHB0 as (SHZ & _).

  assert (BPD : 0 <= bp / 8 /\ bp / 8 + 33 <= 2 ^ 44 - 2 ^ 20) by (clear - B0 B1 B2 FS5; Z.div_mod_to_equations; lia).

  assert (SHP : P / 8 + 34 <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= P / 8) by (apply (SHS P 272 P8); [clear; lia | clear - P2 P3 SFS; lia]).
  assert (SHE : E / 8 + 2 <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= E / 8) by (apply (SHS E 16 E8); [clear; lia | clear - E2 E3 SFS; lia]).
  assert (SHV : V / 8 + 1 <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= V / 8) by (apply (SHS V 8 V8); [clear; lia | clear - V2' V3 SFS; lia]).
  assert (SHBB : bp / 8 + 33 <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= bp / 8) by (apply (SHS bp 264 B8'); [clear; lia | clear - FBS B2; lia]).
  assert (SHC : ch / 8 + chg <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= ch / 8).
  { destruct WC as [(X0 & X1 & X2 & X3)|(X0 & X1 & X2 & X3 & X4 & X5)].
    - left. rewrite X2, X3. change (0 / 8) with 0. clear - S0. pose proof (Z.div_pos sbp 8 ltac:(lia) ltac:(lia)). lia.
    - rewrite X2. apply (SHS ch 16384 (CHA.mod8_of_16 _ X3)); [clear; lia | clear - X5; lia]. }
  assert (SHPK : forall k, 0 <= k < 272 -> (P + k) / 8 + 1 <= sbp / 8 \/ sbp / 8 + (sc + 7) / 8 <= (P + k) / 8).
  { intros k Hk. rewrite (DIV8K P k P8). assert (K8 : 0 <= k / 8 <= 33) by (clear - Hk; Z.div_mod_to_equations; lia). clear - SHP K8. lia. }
  unfold PSOK.BLOCKS_KN0, CCA.vis. fold Hv.

  apply Forall_cons; [apply (KR segs Ex _ xk (bc / 2)); [exact XK | clear - B2 B3; Z.div_mod_to_equations; lia]|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ UKM); clear - BSZ B3; lia|].
  apply Forall_cons; [apply (KA segs Ex _ _ _ _ U2K); [clear; lia | exact B8]|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ XSIZE); clear - SZ; lia|].

  apply Forall_cons; [apply (KW8 segs Ex Hv Mx _ 0 (ELit 0) _ 0 USZ (UL 0 ltac:(clear; lia))); [clear - B0 B1 B2 FS5 BSZ; lia | clear - B0 B1 B2 FS5 BSZ; lia | |]|].
  { apply (CL5A.visr_sub Hv bp bc); [exact (VISB bp bc INB) | clear - BSZ; lia | clear - BSZ; lia]. }
  { rewrite Z.add_0_r. exact NUL. }

  apply Forall_cons; [apply (KWR segs Ex Hv Mx xp 0 _ bp bc XP U2K); [clear - B0 B1 B2 FS5; lia | clear - B0 B1 B2 FS5; lia | clear - B0 B1 B2 FS5; lia | rewrite Z.add_0_r; exact (VISB bp bc INB) | rewrite Z.add_0_r; exact BDEF]|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ XP); clear - B0 B1 B2 FS5; lia|].
  apply Forall_cons; [apply (KA segs Ex _ _ _ _ XP); [clear; lia | exact B16]|].

  apply Forall_cons; [apply (KZsh segs Ex Hv Mx xp (ELit 33) bp 33 XP (UL 33 ltac:(clear; lia))); [clear; lia | clear - B0 B1 B2 FS5; lia | |]|].
  { intros j Hj. apply (VISBS bp bc _ INB). unfold in_shadow_of, S.
    assert (X : 32 <= (bc - 1) / 8) by (clear - B2; Z.div_mod_to_equations; lia).
    replace (bp + bc - 1) with (bp + (bc - 1)) by (clear; lia). rewrite (DIV8K bp (bc - 1) B8'). clear - Hj X. lia. }
  { intros j Hj. apply SHZ. assert (X : 33 <= bc / 8) by (clear - B2; Z.div_mod_to_equations; lia). clear - Hj X. lia. }

  apply Forall_cons; [apply (KD segs Ex _ (ELit 0) 2147446784 (ELit 17592186048512) xp 0 (APC.escale 2 xk) 0 17592186048512 bp bc (UL 0 ltac:(clear; lia)) (UL 17592186048512 ltac:(clear; lia)) XP U2K); clear - BBS; lia|].

  apply Forall_cons; [apply (KU segs Ex Hv Mx xsb 0 xscap sbp sc XSB XSCAP); [clear - S0 S1 S2 FS5; lia | clear - S0 S1 S2 FS5; lia | clear - S0 S1 S2 FS5; lia | rewrite Z.add_0_r; exact (VISB sbp sc INS) | rewrite Z.add_0_r; exact SDEF]|].
  apply Forall_cons; [apply (KWR segs Ex Hv Mx xsb 0 xscap sbp sc XSB XSCAP); [clear - S0 S1 S2 FS5; lia | clear - S0 S1 S2 FS5; lia | clear - S0 S1 S2 FS5; lia | rewrite Z.add_0_r; exact (VISB sbp sc INS) | rewrite Z.add_0_r; exact SDEF]|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ XSB); clear - S0 S1 S2 FS5; lia|].
  apply Forall_cons; [apply (KA segs Ex _ _ _ _ XSB); [clear; lia | exact S8']|].
  apply Forall_cons; [apply (KD segs Ex _ (ELit 0) 2147446784 (ELit 17592186048512) xsb 0 xscap 0 17592186048512 sbp sc (UL 0 ltac:(clear; lia)) (UL 17592186048512 ltac:(clear; lia)) XSB XSCAP); clear - SBS; lia|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ XSLEN); clear - SL1 SL2; lia|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ XSCAP); clear - S2 S3; lia|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ USL); clear - SL1 SL3 S3; lia|].
  apply Forall_cons; [apply (KR segs Ex _ _ _ _ _ XLV); pose proof (Z.mod_pos_bound (PML.ps_level ps1) (2 ^ 32) ltac:(clear; lia)) as X; clear - X; lia|].

  apply Forall_cons; [apply (KD segs Ex _ xp 0 (APC.escale 2 xk) xsb 0 xscap bp bc sbp sc XP U2K XSB XSCAP); clear - FBS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xp 0 (APC.escale 2 xk) (ELit 0) 65536 (ELit 6959104) bp bc 0 6959104 XP U2K (UL 0 ltac:(clear; lia)) (UL 6959104 ltac:(clear; lia))); clear - BIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xsb 0 xscap (ELit 0) 65536 (ELit 6959104) sbp sc 0 6959104 XSB XSCAP (UL 0 ltac:(clear; lia)) (UL 6959104 ltac:(clear; lia))); clear - SIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xp 0 (APC.escale 2 xk) (ELit 0) 6877256 (ELit 2) bp bc 0 2 XP U2K (UL 0 ltac:(clear; lia)) (UL 2 ltac:(clear; lia))); clear - BIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xp 0 (APC.escale 2 xk) (ELit 0) 7015072 (ELit 544) bp bc 0 544 XP U2K (UL 0 ltac:(clear; lia)) (UL 544 ltac:(clear; lia))); clear - BIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xp 0 (APC.escale 2 xk) (ELit 0) 6883756 (ELit 4) bp bc 0 4 XP U2K (UL 0 ltac:(clear; lia)) (UL 4 ltac:(clear; lia))); clear - BIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xsb 0 xscap (ELit 0) 6877256 (ELit 2) sbp sc 0 2 XSB XSCAP (UL 0 ltac:(clear; lia)) (UL 2 ltac:(clear; lia))); clear - SIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xsb 0 xscap (ELit 0) 7015072 (ELit 544) sbp sc 0 544 XSB XSCAP (UL 0 ltac:(clear; lia)) (UL 544 ltac:(clear; lia))); clear - SIMG; lia|].
  apply Forall_cons; [apply (KD segs Ex _ xsb 0 xscap (ELit 0) 6883756 (ELit 4) sbp sc 0 4 XSB XSCAP (UL 0 ltac:(clear; lia)) (UL 4 ltac:(clear; lia))); clear - SIMG; lia|].

  apply Forall_cons; [apply (KDsh1 segs Ex _ xp (ELit 33) (EVar 12) 0 (ELit 16) bp 33 E 16 XP (UL 33 ltac:(clear; lia)) V12 (UL 16 ltac:(clear; lia))); unfold SB; clear - BPD E4; lia|].
  apply Forall_cons; [apply (KDsh1 segs Ex _ xp (ELit 33) (ELit 0) 6877256 (ELit 2) bp 33 0 2 XP (UL 33 ltac:(clear; lia)) (UL 0 ltac:(clear; lia)) (UL 2 ltac:(clear; lia))); unfold SB; clear - BPD; lia|].
  apply Forall_cons; [apply (KDsh1 segs Ex _ xp (ELit 33) (ELit 0) 7015072 (ELit 544) bp 33 0 544 XP (UL 33 ltac:(clear; lia)) (UL 0 ltac:(clear; lia)) (UL 544 ltac:(clear; lia))); unfold SB; clear - BPD; lia|].
  apply Forall_cons; [apply (KDsh1 segs Ex _ xp (ELit 33) (ELit 0) 6883756 (ELit 4) bp 33 0 4 XP (UL 33 ltac:(clear; lia)) (UL 0 ltac:(clear; lia)) (UL 4 ltac:(clear; lia))); unfold SB; clear - BPD; lia|].

  apply Forall_cons; [apply (KDsh2 segs Ex _ (EVar 10) (ELit 34) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) P 34 sbp ((sc + 7) / 8) V10 (UL 34 ltac:(clear; lia)) XSB US7); exact SHP|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (EVar 12) (ELit 2) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) E 2 sbp ((sc + 7) / 8) V12 (UL 2 ltac:(clear; lia)) XSB US7); exact SHE|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (EVar 11) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) V 1 sbp ((sc + 7) / 8) V11 (UL 1 ltac:(clear; lia)) XSB US7); exact SHV|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (EVar 34) (EVar 35) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) ch chg sbp ((sc + 7) / 8) V34 V35 XSB US7); exact SHC|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (APC.eaddz (EVar 10) 209) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (P + 209) 1 sbp ((sc + 7) / 8) (UPK 209 ltac:(clear; lia)) (UL 1 ltac:(clear; lia)) XSB US7); apply SHPK; clear; lia|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (APC.eaddz (EVar 10) 210) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (P + 210) 1 sbp ((sc + 7) / 8) (UPK 210 ltac:(clear; lia)) (UL 1 ltac:(clear; lia)) XSB US7); apply SHPK; clear; lia|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (APC.eaddz (EVar 10) 211) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (P + 211) 1 sbp ((sc + 7) / 8) (UPK 211 ltac:(clear; lia)) (UL 1 ltac:(clear; lia)) XSB US7); apply SHPK; clear; lia|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (APC.eaddz (EVar 10) 212) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (P + 212) 1 sbp ((sc + 7) / 8) (UPK 212 ltac:(clear; lia)) (UL 1 ltac:(clear; lia)) XSB US7); apply SHPK; clear; lia|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (APC.eaddz (EVar 10) 213) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (P + 213) 1 sbp ((sc + 7) / 8) (UPK 213 ltac:(clear; lia)) (UL 1 ltac:(clear; lia)) XSB US7); apply SHPK; clear; lia|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ (APC.eaddz (EVar 10) 220) (ELit 1) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (P + 220) 1 sbp ((sc + 7) / 8) (UPK 220 ltac:(clear; lia)) (UL 1 ltac:(clear; lia)) XSB US7); apply SHPK; clear; lia|].
  apply Forall_cons; [apply (KDsh2 segs Ex _ xp (ELit 33) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) bp 33 sbp ((sc + 7) / 8) XP (UL 33 ltac:(clear; lia)) XSB US7); exact SHBB|].

  apply Forall_cons; [apply (KD segs Ex _ (EVar 2) (-10496) (ELit 10496) xp 0 (APC.escale 2 xk) sp 10496 bp bc V2 (UL 10496 ltac:(clear; lia)) XP U2K); clear - B1 FS3; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 10) 0 (ELit 272) xp 0 (APC.escale 2 xk) P 272 bp bc V10 (UL 272 ltac:(clear; lia)) XP U2K); clear - P2 P3 BFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 12) 0 (ELit 16) xp 0 (APC.escale 2 xk) E 16 bp bc V12 (UL 16 ltac:(clear; lia)) XP U2K); clear - E2 E3 BFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 11) 0 (ELit 8) xp 0 (APC.escale 2 xk) V 8 bp bc V11 (UL 8 ltac:(clear; lia)) XP U2K); clear - V2' V3 BFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 11) 8 (ELit 40) xp 0 (APC.escale 2 xk) V 40 bp bc V11 (UL 40 ltac:(clear; lia)) XP U2K); clear - V2' V3 BFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 36) 0 (EVar 32) xp 0 (APC.escale 2 xk) wp0 wlen bp bc V36 V32 XP U2K); clear - WC B0; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 2) (-10496) (ELit 10496) xsb 0 xscap sp 10496 sbp sc V2 (UL 10496 ltac:(clear; lia)) XSB XSCAP); clear - S1 FS3; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 10) 0 (ELit 272) xsb 0 xscap P 272 sbp sc V10 (UL 272 ltac:(clear; lia)) XSB XSCAP); clear - P2 P3 SFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 12) 0 (ELit 16) xsb 0 xscap E 16 sbp sc V12 (UL 16 ltac:(clear; lia)) XSB XSCAP); clear - E2 E3 SFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 11) 0 (ELit 8) xsb 0 xscap V 8 sbp sc V11 (UL 8 ltac:(clear; lia)) XSB XSCAP); clear - V2' V3 SFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 11) 8 (ELit 40) xsb 0 xscap V 40 sbp sc V11 (UL 40 ltac:(clear; lia)) XSB XSCAP); clear - V2' V3 SFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 36) 0 (EVar 32) xsb 0 xscap wp0 wlen sbp sc V36 V32 XSB XSCAP); clear - WC S0; lia|].
  apply Forall_nil.
Qed.

Lemma FSH_ok : kentry_ok segs Ex (CCA.vis Ax mx Mx)
  (KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3))).
Proof.
  destruct FX as [_ _ _ _ _ FSt _ _ _ _]. destruct FSt as (S0 & S1 & S16 & (S2 & S3) & SBS & SIMG & SFS & _).
  destruct (kF KF) as (F0 & F1 & F64). pose proof (CHA.mod8_of_64 _ F64) as F8. unfold FS_BYTES in SFS.
  unfold CCA.vis. fold Hv.
  apply (KDsh2 segs Ex _ (EVar 65) (ELit 128) xsb (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3)) (CL5A.uv Ex (EVar 65)) 128 sbp ((sc + 7) / 8) eq_refl (uv_lit Ex 128 ltac:(clear; lia)) XSB USC7).
  apply (SHS _ 1024 F8); [clear; lia | clear - F0 F1 SFS; lia].
Qed.
Lemma KN_split : PSOK.BLOCKS_KN xk xsize xp xsb xslen xscap xlevel = firstn 43 (PSOK.BLOCKS_KN0 xk xsize xp xsb xslen xscap xlevel)
  ++ KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap 7) (ELit 3))
  :: skipn 43 (PSOK.BLOCKS_KN0 xk xsize xp xsb xslen xscap xlevel).
Proof. reflexivity. Qed.
Lemma BLOCKS_KN_ok : Forall (kentry_ok segs Ex (CCA.vis Ax mx Mx)) (PSOK.BLOCKS_KN xk xsize xp xsb xslen xscap xlevel).
Proof.
  pose proof BLOCKS_KN0_ok as K0. rewrite <- (firstn_skipn 43 (PSOK.BLOCKS_KN0 xk xsize xp xsb xslen xscap xlevel)) in K0.
  apply Forall_app in K0 as [K1 K2]. rewrite KN_split. apply Forall_app. split; [exact K1|]. apply Forall_cons; [exact FSH_ok | exact K2].
Qed.

Lemma BLOCKS_KDISJ_F_ok : Forall (kentry_ok segs Ex (CCA.vis Ax mx Mx)) (PSOK.BLOCKS_KDISJ_F xp xk xsb xscap).
Proof.
  pose proof FX as FXX. destruct FXX as [_ _ _ _ FB FSt _ _ _ _].
  destruct FB as (B0 & B1 & B16 & (B2 & B3) & B8 & BBS & BIMG & BFS & _). destruct FSt as (S0 & S1 & S16 & (S2 & S3) & SBS & SIMG & SFS & _).
  destruct (kF KF) as (F0 & F1 & F64). destruct (kFL KF) as (L0 & L1). pose proof (CHA.mod8_of_64 _ F64) as F8. unfold FS_BYTES in BFS, SFS.
  pose proof UK2 as U2K. assert (UL : forall z, 0 <= z < 2 ^ 64 -> CL5A.uv Ex (ELit z) = z) by (intros z Hz; exact (uv_lit Ex z Hz)).
  unfold PSOK.BLOCKS_KDISJ_F, CCA.vis. fold Hv.
  apply Forall_cons; [apply (KD segs Ex _ (EVar 65) 0 (ELit 1024) xp 0 (APC.escale 2 xk) _ 1024 bp bc eq_refl (UL 1024 ltac:(clear; lia)) XP U2K); clear - F0 F1 BFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 65) 0 (ELit 1024) xsb 0 xscap _ 1024 sbp sc eq_refl (UL 1024 ltac:(clear; lia)) XSB XSCAP); clear - F0 F1 SFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 60) 0 (ELit 1) xp 0 (APC.escale 2 xk) _ 1 bp bc eq_refl (UL 1 ltac:(clear; lia)) XP U2K); clear - L0 L1 BFS; lia|].
  apply Forall_cons; [apply (KD segs Ex _ (EVar 60) 0 (ELit 1) xsb 0 xscap _ 1 sbp sc eq_refl (UL 1 ltac:(clear; lia)) XSB XSCAP); clear - L0 L1 SFS; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (KDsh2 segs Ex _ (EVar 65) (ELit 128) xp (ELit 33) (CL5A.uv Ex (EVar 65)) 128 bp 33 eq_refl (UL 128 ltac:(clear; lia)) XP (UL 33 ltac:(clear; lia))).
  destruct (SHB _ 1024 F8 ltac:(clear; lia) ltac:(clear - F0 F1 BFS; lia)) as [X|X]; [left; exact X|right].
  assert (Y : 33 <= (bc + 7) / 8) by (clear - B2; Z.div_mod_to_equations; lia). clear - X Y. lia.
Qed.

End K.

Arguments FX {SCFG_P I Ex Mx Ax mx FFx LKx crx ps1 mw bp bc sbp sc xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap} KH.
Arguments PCONST_ok {SCFG_P I Ex Mx Ax mx FFx LKx crx ps1 mw bp bc sbp sc xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap} KH.
Arguments PSTATE_ok {SCFG_P I Ex Mx Ax mx FFx LKx crx ps1 mw bp bc sbp sc xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap} KH.
Arguments BLOCKS_KN0_ok {SCFG_P I Ex Mx Ax mx FFx LKx crx ps1 mw bp bc sbp sc xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap} KH.
Arguments BLOCKS_KN_ok {SCFG_P I Ex Mx Ax mx FFx LKx crx ps1 mw bp bc sbp sc xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap} KH KF.
Arguments BLOCKS_KDISJ_F_ok {SCFG_P I Ex Mx Ax mx FFx LKx crx ps1 mw bp bc sbp sc xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap} KH KF.
End PSOKK.
