(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec Frame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf AXImgKit X8Kit X8LeafKit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst
     X8_rsfree X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_A_kit4 X8_A_kit3 X8_S_kit X8_S_kit3 X8_S_rs2 X8_R_read X8_R_readC X8_R_readF X8_R_readD X8_R_readE
     X8_read_stmt X8_read2 X8_read3 X8_read3b X8_read4 X8_read4b X8_read5 X8_read5b.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis FS0 : stack_malloc_0_stmt H.
  Hypothesis HH7 : asan_rt_hyps7 H.
  Hypothesis HH8 : asan_rt_hyps8 H.
  Hypothesis BPUT : forall MX CX MA R, bput_stmtR H MX CX MA R.

(* [comment removed for export] *)
Lemma bput_stmtR_of : forall MX CX MA R, bput_stmt H MX CX MA R -> bput_stmtR H MX CX MA R.
Proof. intros MX CX MA R K. exact K. Qed.

Lemma rs_done_mono : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M1 M0 : Z) (cf : config),
  rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 cf -> M1 <= M0 ->
  rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 M0 cf D LE. unfold rs_done in *.
  destruct D as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & w & s & errv & E & tot & XS & D).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m, w, s, errv, E, tot, XS.
  destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16).
  repeat (split; [assumption|]). split; [clear - D15 LE; lia|].
  intros K1 K2. destruct (D16 K1 K2) as [K3 K4]. split; [clear - K3 LE; lia | exact K4].
Qed.

(* [comment removed for export] *)
Lemma rs_read_round : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R -> bv_unsigned ra mod 2 = 0 ->
  rs_at_doread H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (fun cf' => rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf'
                      \/ exists M1 w', M1 < M0 /\ rs_at_put H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 w' cf') cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC R0 RA AT.
  eapply (ah_seq H HH); [exact (rs_read_A H HH FS0 HH7 HH8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 AT)|].
  intros cf1 (w1 & _ & AT1).
  eapply (ah_seq H HH); [exact (rs_read_B1 H HH FS0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 AT1)|].
  intros cf2 (n & eof & _ & AT2). exact (rs_read_B2 H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 RA AT2).
Qed.

(* [comment removed for export] *)
Lemma rs_loop : forall (n : nat) (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R -> bv_unsigned ra mod 2 = 0 -> M0 < Z.of_nat n ->
  rs_at_doread H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf ->
  as_SR H (rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0) cf.
Proof.
  induction n as [|n IH]; intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w cf STC PLC R0 RA LT AT.
  - exfalso. pose proof AT as AT'. unfold rs_at_doread, rs_core in AT'.
    destruct AT' as (rax & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s0x & s9x & t3 & t4 & t5 & t6 & m & s & errv & E & tot & mw1 & mw2 & t2c & optc & XS
                     & _ & _ & _ & _ & _ & WM0).
    destruct C as [bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
    unfold rs_static in STC. cbn_w_all.
    destruct STC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NR & _). unfold wM in WM0. clear - WM0 NR LT. unfold zlength in WM0. cbn in LT. nia.
  - eapply (ah_seq H HH); [exact (rs_read_round _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 RA AT)|].
    intros cf1 [D | (M1 & w1 & LT1 & AP)]; [apply (ah_done H HH); exact D|].
    eapply (ah_seq H HH); [exact (rs_put_round H HH BPUT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC PLC R0 RA AP)|].
    intros cf2 [D | (w2 & _ & AD)]; [apply (ah_done H HH); eapply rs_done_mono; [exact D | clear - LT1; lia]|].
    eapply (ah_mono H HH); [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 w2); [exact STC | exact PLC | exact R0 | exact RA | clear - LT LT1; lia | exact AD]|].
    intros cf3 D. eapply rs_done_mono; [exact D | clear - LT1; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem hread_spec : forall MA MR, hread_stmt H MA MR.
Proof.
  intros MA MR C ra sp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 msF m mo fr w s errv E XS
         VIS STC PLC NS11 RM RP ALK ST FR0 SZFR FXS XP0 NRB KREL MP RA.
  pose proof STC as STC0. pose proof PLC as PLC0. pose proof RP as RP0.
  destruct C as [bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn Ag].
  unfold rs_static in STC. unfold rs_placed in PLC. unfold RWm in RM. unfold RWp in RP. cbn_w_all.
  cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct STC as (AOP & AOE & P8 & E8 & BS8 & FB8 & SEPPE & SEPBF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL).
  destruct PLC as (SOB & SOF & LOS & SP16 & SPHI & SPB & SPC & FRB128 & FRF128).
  destruct RM as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HCT & FTS & MV & FBU & EC & BSC & SB & HP & ERR & AUX & MI & RF & AC & SK & ATH & ACP & ACE & SVE & ACB & ACF & SVA).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM_ & FRF & DJL & DJB & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  assert (R0 : 0 <= MR) by (destruct ALK as (_ & K & _); exact K).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof aceil_facts as (AF1 & AF2 & AF3). unfold HREAD_STACK in LOS. pose proof BPUT_STACK_val as BSV.
  assert (AIS : AINTRIN_STACK = 4096) by reflexivity.
  subst tp. assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; clear; lia). rewrite EA in ERR.
  pose proof SOB as SOB0. pose proof SOF as SOF0. unfold sobj in SOB, SOF.
  pose proof (AFlatBuf_shape _ _ _ _ _ FBU) as (B0 & BIO & BOLE & BCE & FS5).
  assert (SUBin : forall b, In b LBin -> In b (LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOP ltac:(intros b [])) as AOPn. pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOE ltac:(intros b [])) as AOEn.
  pose proof (aapp_bounds _ _ (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOPn) ltac:(clear; lia)) as (PQ1 & PQ2 & PQ3 & PQ4 & _).
  pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF AOEn) as APE. pose proof (aapp_bounds _ _ APE ltac:(clear; lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof UW as UWc. unfold PutUw in UWc. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UWc.
  destruct UWc as (FC & HDR & USED & MB & RD & MRG & CBH & CBB & PFT & FI & AXS).
  destruct (rw_cells_forget _ _ _ _ EC) as [ej ECb]. cbn [cells_size csize Nat.add ErrCodeCells length] in ECb.
  (* [comment removed for export] *)
  eapply (ahh_evt_then H HH); [exact KREL| exact VIS| |].
  { eapply (rs_entry H HH ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo shi Ev bs fb P FB ej);
      [ exact (proj1 FBU) | exact FB8 | clear - SOF; lia | clear - SOF; lia
      | exact ECb | exact APE | exact ACE | exact SVE | exact E8
      | exact B0 | exact BIO | clear - BOLE; lia | exact BCE
      | clear - SOB AF1; unfold AAPP_HI in *; lia | clear - PQ4 PQ3; unfold AAPP_HI in *; lia
      | exact ST | clear - LOS BSV AIS; lia | exact CEIL | exact MI | exact AC | exact SK ]. }
  intros msF1 mo1 KREL1 MP1 (m1 & jm1 & jm2 & jt2 & jopt & rax & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & MU1 & WM1 & MI1 & ST1 & FRM1 & SAVED1 & FBC1 & EC1 & AC1 & ALT).
  (* [comment removed for export] *)
  assert (AW : Forall awin [(lo, bv_unsigned sp); (Ev, Ev + 24)]%Z)
    by (apply Forall_cons; [apply awin_stack; exact CEIL| apply Forall_cons; [eapply awin_aapp; [exact APE| clear; lia| clear; lia]| apply Forall_nil]]).
  assert (DJ : forall A0 n0, (A0 + n0 <= lo \/ bv_unsigned sp <= A0) -> (A0 + n0 <= Ev \/ Ev + 24 <= A0) -> disjoint_from [(lo, bv_unsigned sp); (Ev, Ev + 24)]%Z A0 n0)
    by (intros A0 n0 K1 K2; cbn; split; [exact K1| split; [exact K2| exact I]]).
  destruct (stack_window_ok' H HH s (LBn ++ LBin) m LF lo (bv_unsigned sp) HP CEIL) as (V1 & V2 & V3).
  destruct (aobj_write_ok H HH _ _ _ _ _ _ _ HP RF AOEn) as (VE1 & VE2 & VE3).
  destruct (client_frame3 H HH _ _ _ _ _ _ HP RF AC MU1 WM1
              ltac:(apply Forall_cons; [exact V1| apply Forall_cons; [exact VE1| apply Forall_nil]])
              ltac:(apply Forall_cons; [exact V2| apply Forall_cons; [exact VE2| apply Forall_nil]])
              ltac:(apply Forall_cons; [exact V3| apply Forall_cons; [exact VE3| apply Forall_nil]])) as (HP1 & RF1 & _).
  pose proof (ah_rauxv_frame H HH _ _ _ _ _ AUX MU1 WM1 ltac:(apply Forall_cons; [exact V1| apply Forall_cons; [exact VE1| apply Forall_nil]])) as AUX1.
  pose proof (ah_thr H HH _ _ _ HP1) as ATH1.
  assert (SK1 : stack0 m1 lo shi).
  { eapply stack0_transport; [exact SK| exact MU1| exact WM1|].
    apply Forall_cons; [apply stack0_ok_app; cbn [fst snd]; unfold AHI_LO; clear - CEIL AF1 SPR; lia|].
    apply Forall_cons; [eapply stack0_ok_aapp; [exact APE| cbn [fst snd]; clear; lia| cbn [fst snd]; clear; lia]| apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (XPP : forall A0 cs, rw_cells asegs m A0 cs -> P <= A0 -> A0 + Z.of_nat (cells_size cs) <= P + 352 -> rw_cells asegs m1 A0 cs).
  { intros A0 cs K Q1 Q2. eapply (rw_cells_transport asegs); [exact K| exact MU1| exact WM1|]. apply DJ; [left; clear - Q2 PQ2 CEIL; lia| clear - Q1 Q2 SEPPE; lia]. }
  pose proof (XPP _ _ PC ltac:(clear; lia) ltac:(cbn; clear; lia)) as PC1.
  pose proof (XPP _ _ HDR ltac:(unfold O_PR_HDR; clear; lia) ltac:(unfold O_PR_HDR; cbn; clear; lia)) as HDR1.
  pose proof (XPP _ _ USED ltac:(unfold O_PR_USED; clear; lia) ltac:(unfold O_PR_USED; cbn; clear; lia)) as USED1.
  pose proof (XPP _ _ RD ltac:(clear; lia) ltac:(cbn; clear; lia)) as RD1.
  pose proof (XPP _ _ MRG ltac:(unfold O_PR_MERGE; clear; lia) ltac:(unfold O_PR_MERGE; cbn; clear; lia)) as MRG1.
  pose proof (XPP _ _ CBH ltac:(clear; lia) ltac:(cbn; clear; lia)) as CBH1. pose proof (XPP _ _ CBB ltac:(clear; lia) ltac:(cbn; clear; lia)) as CBB1.
  pose proof (XPP _ _ RDI ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDI1.
  pose proof (XPP _ _ J13 ltac:(clear; lia) ltac:(cbn; clear; lia)) as J13'. pose proof (XPP _ _ J32a ltac:(clear; lia) ltac:(cbn; clear; lia)) as J32a'.
  pose proof (XPP _ _ J8a ltac:(clear; lia) ltac:(cbn; clear; lia)) as J8a'. pose proof (XPP _ _ J32b ltac:(clear; lia) ltac:(cbn; clear; lia)) as J32b'.
  pose proof (XPP _ _ J8b ltac:(clear; lia) ltac:(cbn; clear; lia)) as J8b'.
  destruct OFFP as (OPe & OPb & OPt & OPm). destruct OFFE as (OEe & OEb & OEt & OEm).
  assert (FC1 : AFieldsC m1 (P + 80) S L ns ls em).
  { eapply AFieldsC_transport_gen; [exact FC| exact MU1| exact WM1| | |].
    - apply DJ; [left; clear - PQ2 CEIL; lia| clear - SEPPE; lia].
    - intros x Hx. pose proof (sh_ge_lowsh x ltac:(clear - Hx PQ4; lia)) as SL. pose proof (sh_nsh_high x 1 ltac:(clear - Hx PQ4; lia) ltac:(clear; lia) ltac:(clear - Hx PQ3; unfold AAPP_HI in *; lia)) as SU.
      unfold nsh in SU. change ((1 + 7) / 8) with 1 in SU. pose proof (aapp_not_shadowland _ _ APE) as NE'.
      cbn [outside fst snd]. unfold ALOWSH_LO, AHI_LO in *. clear - SL SU NE' CEIL AF1. repeat split; lia.
    - intros e dd Ld. destruct (em_elem_facts _ _ _ _ _ _ _ _ _ FC Ld) as (G0 & G1 & G2 & G3 & G4).
      split; [apply DJ; [left; clear - G2 CEIL; lia| destruct (OEe e dd Ld) as [K|K]; [right| left]; clear - K; lia]|].
      pose proof (sh_ge_lowsh e ltac:(clear - G0; lia)) as SL. pose proof (sh_nsh_high e (esize dd) ltac:(clear - G0; lia) ltac:(clear - G1; lia) ltac:(clear - G2 AF1; unfold AAPP_HI; lia)) as SU.
      pose proof (aapp_not_shadowland _ _ APE) as NE'. cbn [disjoint_from fst snd]. unfold ALOWSH_LO, AHI_LO in *. clear - SL SU NE' CEIL AF1. repeat split; lia. }
  assert (MB1 : AMBuf m1 (P + 168) es insz).
  { eapply AMBuf_transport_win; [exact MB| exact MU1| exact WM1|]. pose proof (AMBraw_addr_ok _ _ _ _ _ _ _ (proj1 MB)) as AOK.
    apply Forall_cons; [apply mwin_stack; [exact AOK| exact CEIL]|].
    apply Forall_cons; [| apply Forall_nil]. split; [eapply awin_aapp; [exact APE| clear; lia| clear; lia]|]. cbn [fst snd]. split; [clear - SEPPE; lia|].
    intros x sz IN. destruct (OEb x sz IN) as [K|K]; [right| left]; clear - K; lia. }
  assert (PFT1 : APfTab m1).
  { unfold APfTab in PFT |- *. eapply (rw_cells_transport asegs); [exact PFT| exact MU1| exact WM1|]. apply DJ; left; unfold APF_TABPTR, AIMG_TOP in *; cbn; [clear - CEIL AF1| clear - R1]; lia. }
  assert (FI1 : FTInit m1).
  { eapply FTInit_transport; [exact FI| exact MU1|]. apply DJ; left; unfold P_A_FT_INIT, AIMG_TOP in *; [clear - CEIL AF1| clear - R1]; lia. }
  assert (AXS1 : AXStatics2 m1).
  { eapply AXStatics2_transport; [exact AXS| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; left; unfold AIMG_TOP in *; [clear - CEIL AF1| clear - R1]; lia. }
  assert (HOWN1 : HdrOwnA (LBn ++ LBin) m1 h).
  { assert (K : forall ptr len, ASvOwn (LBn ++ LBin) m ptr len -> (len <> 0 -> Ev + 24 <= ptr \/ ptr + len <= Ev) -> ASvOwn (LBn ++ LBin) m1 ptr len).
    { intros ptr len [Z0|(L1 & p & bsx & IN & CE & AD)] SE'; [left; exact Z0| right]. split; [exact L1|]. exists p, bsx.
      pose proof (ah_blocks H HH _ _ _ _ HP IN) as (_ & _ & _ & _ & B5 & _). cbn [blk_addr blk_size fst snd] in B5.
      split; [exact IN|]. split.
      - eapply (rw_cells_transport asegs); [exact CE| exact MU1| exact WM1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - L1; lia).
        apply DJ; [left; clear - B5 CEIL; lia| destruct (SE' ltac:(clear - L1; lia)) as [Q|Q]; [right| left]; clear - Q; lia].
      - eapply addressable_transport_awin'; [exact AD| exact MU1| exact WM1| exact AW| clear - B5 AF1; unfold AAPP_HI; lia]. }
    destruct HOWN as (O1 & O2 & O3 & O4). split; [exact (K _ _ O1 OEm)|]. split; [exact (K _ _ O2 OEt)|]. split; [exact O3| exact O4]. }
  assert (HCT1 : AHttpCat m1 g).
  { eapply AHttpCat_transport; [exact HCT| exact MU1| exact WM1| |]; apply DJ; left; unfold AG_HTTP_CAT, AG_HTTP_CAT_GUARD, AIMG_TOP in *; first [clear - CEIL AF1; lia| clear - R1; lia]. }
  assert (FTS1 : AFieldTabZero m1 \/ FT m1).
  { eapply FTState_transport; [exact FTS| exact MU1| exact WM1|]. apply DJ; left; unfold AG_FIELD_TABLE, AIMG_TOP in *; [clear - CEIL AF1| clear - R1]; lia. }
  assert (MV1 : AMiscVt48 m1).
  { unfold AMiscVt48 in MV |- *. eapply (ro_cells_transport asegs); [exact MV| exact MU1|]. apply DJ; left; unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR, AIMG_TOP in *; cbn; [clear - CEIL AF1| clear - R1]; lia. }
  assert (FBU1 : AFlatBuf (LBn ++ LBin) m1 fb FB fds).
  { eapply AFlatBuf_transport_awin; [exact FBU| exact MU1| exact WM1| exact AW| apply DJ; [right; clear - FRF128; lia| right; unfold SZ_FB; clear - R2 CEIL LOS BSV FRF128; lia]|].
    intros NE. destruct FS5 as [K|(BP & _ & BCP & BAP & pf0 & INf0)]; [exfalso; exact (NE K)|].
    pose proof (ah_blocks H HH _ _ _ _ HP INf0) as (_ & _ & _ & _ & G5 & _). cbn in G5.
    apply DJ; [left; clear - G5 CEIL; lia| pose proof (fobj_off_block H HH _ _ _ _ _ _ _ _ _ _ HP RF AOE INf0) as Q; clear - Q; lia]. }
  assert (BSC1 : rw_cells asegs m1 bs (BasicStreamCells stb)) by (eapply (rw_cells_transport asegs); [exact BSC| exact MU1| exact WM1| apply DJ; right; [clear - FRB128; lia| clear - R2 CEIL LOS BSV FRB128; lia]]).
  pose proof (ah_blocks H HH _ _ _ _ HP (SUBin _ INS)) as (T1 & _ & _ & T4 & T5 & _). cbn in T1, T4, T5.
  assert (SB1 : AStateBlock (LBn ++ LBin) m1 stb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds).
  { eapply AStateBlock_transport_awin; [exact SB| exact MU1| exact WM1| exact AW| |].
    - apply DJ; [left; clear - T5 CEIL; lia| pose proof (fobj_off_block H HH _ _ _ _ _ _ _ _ _ _ HP RF AOE (SUBin _ INS)) as Q; clear - Q; lia].
    - cbn [st_fb]. intros NEs. destruct STRM as [[_ EFs]|(N1 & SA & SE)]; [exfalso; exact (NEs EFs)|]. unfold fb_cap. rewrite SA, SE.
      destruct (INA N1) as [p9 IN9]. pose proof (ah_blocks H HH _ _ _ _ HP (SUBin _ IN9)) as (_ & _ & _ & _ & A5 & _). cbn in A5.
      replace (A + N - A) with N by (clear; lia).
      apply DJ; [left; clear - A5 CEIL; lia| pose proof (fobj_off_block H HH _ _ _ _ _ _ _ _ _ _ HP RF AOE (SUBin _ IN9)) as Q; clear - Q; lia]. }
  assert (ERR1 : rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]).
  { rewrite EA. eapply (rw_cells_transport asegs); [exact ERR| exact MU1| exact WM1|]. apply DJ; left; unfold AERRNO, ATP, AIMG_TOP in *; cbn; [clear - CEIL AF1| clear - R1]; lia. }
  pose proof (acc_transport_awin _ _ _ _ _ ACP MU1 AW) as ACP1. pose proof (acc_transport_awin _ _ _ _ _ ACE MU1 AW) as ACE1.
  pose proof (acc_transport_awin _ _ _ _ _ ACB MU1 AW) as ACB1. pose proof (acc_transport_awin _ _ _ _ _ ACF MU1 AW) as ACF1.
  pose proof (aobj_shvis H HH _ _ _ _ _ _ HP1 RF1 AOEn ltac:(clear; lia)) as SVE1.
  assert (SVA1 : 1 <= N -> shvis m1 A (A + N)) by (intros N1; destruct (INA N1) as [p9 IN9]; exact (ah_blk_shvis H HH _ _ _ _ _ _ HP1 (SUBin _ IN9))).
  assert (FR0' : rw_cells asegs m1 (bv_unsigned sp) fr) by (eapply (rw_cells_transport asegs); [exact FR0| exact MU1| exact WM1| apply DJ; right; [clear; lia| clear - R2 CEIL LOS BSV; lia]]).
  assert (XP1 : xpres H LBin SP (hread_X P Ev fb stb [] [] ++ XS) m0 m1).
  { eapply xpres_trans; [exact XP0|].
    eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP| exact MU1| exact WM1|] | clear; lia| exact SUBin| intros a K; exact K].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
    - left. clear - CEIL SPC. lia.
    - right. intros a Ha. unfold hread_X, put_X. cbn. do 3 right. left. exact Ha. }
  assert (RM1 : RWm H (mkC bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp (Z_to_bv 64 ATP) F fc MXc CXc)
                     (mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr) s errv EC_clear m1).
  { unfold RWm, PutUw. cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
    split; [exact PC1|]. split; [exact (conj FC1 (conj HDR1 (conj USED1 (conj MB1 (conj RD1 (conj MRG1 (conj CBH1 (conj CBB1 (conj PFT1 (conj FI1 AXS1))))))))))|].
    split; [exact HOWN1|]. split; [exact RDI1|]. split; [exact J13'|]. split; [exact J32a'|]. split; [exact J8a'|]. split; [exact J32b'|]. split; [exact J8b'|].
    split; [exact HCT1|]. split; [exact FTS1|]. split; [exact MV1|]. split; [exact FBU1|]. split; [exact EC1|]. split; [exact BSC1|]. split; [exact SB1|].
    split; [exact HP1|]. split; [exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|]. split; [exact RF1|]. split; [exact AC1|]. split; [exact SK1|]. split; [exact ATH1|].
    split; [exact ACP1|]. split; [exact ACE1|]. split; [exact SVE1|]. split; [exact ACB1|]. split; [exact ACF1| exact SVA1]. }
  set (C := mkC bs fb P Ev ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp (Z_to_bv 64 ATP) F fc MXc CXc) in *.
  set (w0 := mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr) in *.
  assert (WMN : 0 <= wM N w0) by (subst w0; unfold wM; cbn_w; clear - NR; unfold zlength; nia).
  destruct FRM1 as (LOC1 & MID1 & MSZa & MSZb & SHE1 & T21 & SZ21 & OPT1 & SZO1).
  destruct ALT as [[Z0 EMS] | [POS EMS]].
  - (* [comment removed for export] *)
    eapply (rs_loop (Datatypes.S (Z.to_nat (wM N w0))) C MA MR sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra fr (wM N w0) w0);
      [exact STC0 | exact PLC0 | exact R0 | exact RA | clear - WMN; lia |].
    unfold rs_at_doread, rs_core, rs_frames. subst C w0. cbn_w. cbn [cfg_ms cfg_model ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
    exists rax, u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, s0, s9, u3, u4, u5, u6, m1, s, errv, EC_clear, 0, (CB 8 jm1), (CB 8 jm2), [CB 24 jt2], [CB 24 jopt], XS.
    split; [exact EMS|]. split; [exact NS11|]. split; [exact KREL1|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP1)|].
    split; [| clear; lia].
    split; [exact RM1|]. split; [exact RP0|]. split; [exact ALK|]. split; [exact ST1|].
    split; [split; [split; [exact LOC1| split; [exact MID1| split; [exact MSZa| split; [exact MSZb| split; [exact SHE1| split; [exact T21| split; [exact SZ21| split; [exact OPT1| exact SZO1]]]]]]]]| split; [exact SAVED1| split; [exact FR0'| exact SZFR]]]|].
    split; [exact FXS|]. split; [exact XP1|]. split; [clear; lia|]. split; [clear - SZS; lia|]. exact NRB.
  - (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact EMS| |].
    { eapply (rs_parse rax sp gp (Z_to_bv 64 ATP) u0 u1 u2 s0 b0 b1 b2 b3 b4 b5 b6 b7 (wz (Ev + 8)) (wz (Ev + 16)) s9 u3 u4 u5 u6 F fc m1 lo shi Ev bs fb P 0 FB (CB 8 jm1) (CB 8 jm2) [CB 24 jt2] [CB 24 jopt]);
        [ split; [exact LOC1| split; [exact MID1| split; [exact MSZa| split; [exact MSZb| split; [exact SHE1| split; [exact T21| split; [exact SZ21| split; [exact OPT1| exact SZO1]]]]]]]]
        | exact FBC1 | exact FB8 | clear - SOF; lia | clear - SOF; lia
        | exact B0 | exact BIO | clear - BOLE; lia | exact BCE
        | clear - PQ4 PQ3; unfold AAPP_HI in *; lia | clear; lia
        | clear - LOS BSV; lia | exact CEIL | exact SK1 | exact MI1 ]. }
    intros msF2 mo2 KREL2 MP2 (EMS2 & _ & _ & _).
    eapply (ah_seq H HH).
    { eapply (rs_put_round H HH BPUT C MA MR sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra fr (wM N w0) w0); [exact STC0 | exact PLC0 | exact R0 | exact RA |].
      unfold rs_at_put, rs_core, rs_frames. subst C w0. cbn_w. cbn [cfg_ms cfg_model ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
      exists u0, u1, u2, b4, b5, b6, b7, s0, s9, u3, u4, u5, u6, m1, s, errv, EC_clear, 0, (CB 8 jm1), (CB 8 jm2), [CB 24 jt2], [CB 24 jopt], XS.
      split; [exact EMS2|].
      split; [clear - POS; lia|]. split; [exact NS11|]. split; [exact KREL2|]. split; [exact (ah_mpres_trans H HH _ _ _ MP (ah_mpres_trans H HH _ _ _ MP1 MP2))|].
      split; [| clear; lia].
      split; [exact RM1|]. split; [exact RP0|]. split; [exact ALK|]. split; [exact ST1|].
      split; [split; [split; [exact LOC1| split; [exact MID1| split; [exact MSZa| split; [exact MSZb| split; [exact SHE1| split; [exact T21| split; [exact SZ21| split; [exact OPT1| exact SZO1]]]]]]]]| split; [exact SAVED1| split; [exact FR0'| exact SZFR]]]|].
      split; [exact FXS|]. split; [exact XP1|]. split; [clear; lia|]. split; [clear - SZS; lia|]. exact NRB. }
    intros cf2 [D | (w2 & _ & AD)]; [apply (ah_done H HH); exact D|].
    eapply (rs_loop (Datatypes.S (Z.to_nat (wM N w0)))); [exact STC0 | exact PLC0 | exact R0 | exact RA | clear - WMN; lia | exact AD].
Qed.
End HCW.
