(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec Frame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf AXImgKit X8Kit X8LeafKit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst X8_rsfree X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_A_kit4 X8_A_kit3 X8_S_kit X8_S_kit3 X8_S_rs2 X8_R_read X8_R_readC X8_R_readF X8_R_readD X8_R_readE X8_read_stmt X8_read2 X8_read3 X8_read3b X8_read4 X8_read4b X8_read5.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pst_eof (d : pst) : pst :=
  mkPST (rs_eof_c (ps_c d)) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d) (ps_h d) (ps_u d) (ps_es d) (ps_insz d) (rs_eof_g (ps_c d) (ps_g d)) (ps_rdi d)
        (ps_LBn d) (ps_A d).
Definition w_after_eof (w : rsw) : rsw :=
  mkW (pst_eof (w_d w)) (w_PB w) (w_FBB w) (w_FB w) (w_fds w) (w_Fs w) (w_sds w) (w_nr w).

Lemma rs_eof_c_cases : forall c, rs_eof_c c = c \/ rs_eof_c c = pc_set_state c 11.
Proof.
  intros c. unfold rs_eof_c, peof_res. destruct (pc_state c =? 0); [left; reflexivity|].
  destruct (pc_state c <=? 2); [left; reflexivity|]. destruct (peof_body_flags c); [| right; reflexivity].
  destruct (pc_state c =? 11); left; reflexivity.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

Lemma RWp_eof_post : forall (C : rsc) MA (w : rsw), RWp H C MA w -> RWp H C MA (w_after_eof w).
Proof.
  intros C MA w RP.
  destruct C as [bs fb P E ioc N lo B0 shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m00 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L1 ns ls em h u es insz g rdi LBn Ag].
  unfold w_after_eof, pst_eof, RWp in *. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  pose proof (rs_eof_facts c g PCOK) as (PCOK' & _ & _ & _).
  destruct (rs_eof_c_cases c) as [EC | EC]; rewrite EC in *.
  { repeat (split; [assumption|]). exact AL. }
  unfold pc_set_state in *. cbn [pc_state pc_hlim pc_len pc_skip] in *.
  split; [exact PCOK'|]. split; [exact OWN|]. split; [exact MOWN|]. split; [exact DFB|].
  split; [intros K; exfalso; clear - K; lia|]. split; [exact U01|]. split; [exact CAP|]. split; [exact LES|]. split; [exact INZ|].
  split; [intros K; exfalso; clear - K; lia|]. split; [exact HDJ|]. split; [intros K; exfalso; clear - K; lia|]. split; [exact SK62|].
  split; [exact AOWN|]. split; [exact PERM|]. split; [exact FOK|].
  split; [exact FRL|]. split; [exact FRB|]. split; [exact FRT|]. split; [exact FRM|].
  split; [exact FRF|]. split; [exact DJL|]. split; [exact DJB|]. split; [exact DJT|]. split; [exact DJM|].
  split; [exact OFFP|]. split; [exact OFFE|]. split; [exact STRM|]. split; [exact SZS|]. split; [exact NRK|]. split; [exact CPM|].
  replace (11 <=? 9) with false by reflexivity. replace (11 <=? 1) with false by reflexivity. cbv iota.
  set (s34 := if pc_state c <=? 9 then 34 else 0) in *. set (s8 := if pc_state c <=? 1 then 8 else 0) in *. set (s2 := if pc_state c <=? 9 then 2 else 0) in *.
  assert (0 <= s34) by (subst s34; destruct (pc_state c <=? 9); clear; lia).
  assert (0 <= s8) by (subst s8; destruct (pc_state c <=? 1); clear; lia).
  assert (0 <= s2) by (subst s2; destruct (pc_state c <=? 9); clear; lia).
  split; [clear - BY H0; lia|]. split; [clear - CN H1 H2; lia|]. split; [exact IZ|]. split; [exact AG0|]. clear - AL H0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rs_read_B2 : forall (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw) (eof : bool) (cf : config),
  rs_static H C -> rs_placed C (bv_unsigned sp) -> 0 <= R -> bv_unsigned ra mod 2 = 0 ->
  rs_at_cmp H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w eof cf ->
  as_SR H (fun cf' => rs_done H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 cf'
                      \/ exists M1 w', M1 < M0 /\ rs_at_put H C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M1 w' cf') cf.
Proof.
  intros C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr M0 w eof cf STC PLC R0 RA AT.
  pose proof STC as STC0.
  destruct C as [bs fb P E ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn Ag].
  destruct cf as [msF mo]. unfold rs_at_cmp, rs_frames in AT. unfold rs_static in STC. unfold rs_placed in PLC.
  cbn_w_all. cbn [cfg_ms cfg_model] in AT |- *.
  destruct STC as (AOP & AOE & AOF & P8 & E8 & BS8 & FB8 & SEPPE & SEPPF & SEPEF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL & MB1).
  destruct PLC as (SOB & LOS & SP16 & SPHI & SPB & SPC & FRB128).
  destruct AT as (rax & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & s & errv & tot & k & spa & ff & fp & tmp & gap & optc & hw & j56 & j120 & XS
                  & VIS & NS11 & KREL & MP & RM & RP & ALK & ST & (FRM & SAVED & FR0 & SZFR & FAKE) & FF & (me & RF0) & FXS & FRX & XP0 & TOT0 & TOT & WM0 & CASE).
  pose proof RP as RP0. pose proof RM as RM0. unfold RWmF in RM. unfold RWp in RP. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct RM as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HCT & FTS & MV & FBU & EC & BSC & SB & HP & ERR & AUX & MI & RF' & AC & SK & ATH & ACP & ACE & SVE & ACB & ACF & SVA).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM_ & FRF & DJL & DJB & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof aceil_facts as (AF1 & AF2 & AF3). unfold HREAD_STACK in LOS. pose proof BPUT_STACK_val as BSV.
  assert (AIS : AINTRIN_STACK = 4096) by reflexivity.
  pose proof FRM as ((jl & LOW) & SLOTS & MW80 & MSZ & SH16 & (j96 & J96) & F120 & TMP & TSZ & GAP & GSZ & SPA).
  assert (SPA64 : 0 <= spa < 2^64) by (clear - SPR LOS BSV CEIL AF1 SPA; lia).
  assert (SPACE : aceil <= spa) by (clear - LOS BSV CEIL SPA; lia).
  assert (HI : aceil <= bv_unsigned sp + -104) by (clear - CEIL LOS BSV; lia).
  subst tp. assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; clear; lia). rewrite EA in ERR.
  pose proof SOB as SOB0. unfold sobj in SOB.
  set (LF' := (2, ff, fp) :: LF) in *.
  assert (SUBF : forall f, In f LF -> In f LF') by (intros f Hf; right; exact Hf).
  pose proof (fwin_nums H LF ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & SHFF & SF0 & SF1 & SA & M1 & M2 & LSH & SHH & SIDE & APFF & APP1 & APB).
  assert (F0 : 0 <= ff) by (clear - F1; unfold AIMG_TOP, AFS_HDR in *; lia). assert (F8' : ff mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
  pose proof (AFlatBuf_shape _ _ _ _ _ FBU) as (B0 & BIO & BOLE & BCE & FS5).
  assert (SUBin : forall b, In b LBin -> In b (LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOP ltac:(intros b [])) as AOPn. pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOE ltac:(intros b [])) as AOEn.
  pose proof (aobj_LB_mono _ (LBn ++ LBin) _ _ _ AOF ltac:(intros b [])) as AOFn.
  pose proof (aobj_sub _ _ _ _ P 80 AOPn ltac:(clear; lia) ltac:(clear; lia)) as AOP80.
  pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOPn) as APP0. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOP80) as APP80.
  pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOEn) as APE. pose proof (aobj_aapp H HH _ _ _ _ _ _ _ HP RF0 AOFn) as APF.
  pose proof (aapp_bounds _ _ APP0 ltac:(clear; lia)) as (PQ1 & PQ2 & PQ3 & PQ4 & _).
  pose proof (aapp_bounds _ _ APE ltac:(clear; lia)) as (R1 & R2 & R3 & R4 & R5). pose proof (aapp_bounds _ _ APF ltac:(clear; lia)) as (T1 & T2 & T3 & T4 & T5).
  pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOPn) as FOP. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOEn) as FOE. pose proof (aobj_fsobj H HH _ _ _ _ _ _ HP AOFn) as FOF.
  pose proof UW as UWc. unfold PutUw in UWc. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UWc.
  destruct UWc as (FC & HDR & USED & MB & RD & MRG & CBH & CBB & PFT & FI & AXS).
  assert (KB : 0 <= k < 2^64) by (destruct eof; [destruct CASE as [_ K0]; clear - K0; lia| destruct CASE as (K1 & KS & _); unfold fb_size in KS; clear - K1 KS B0 BIO BOLE BCE AF1; lia]).
  destruct (rw_cells_forget _ _ _ _ (proj1 FBU)) as [fj FBb]. unfold FlatBufCells in FBb. cbn [cells_size csize Nat.add length] in FBb.
  (* [comment removed for export] *)
  eapply (ahh_evt_then H HH); [exact KREL| exact VIS| |].
  { eapply (rs_cmp H HH _ sp gp (Z_to_bv 64 ATP) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc me m LF lo shi spa ff fp E bs fb P tot k eof hw tmp gap optc ect_cells _ j56 j120);
      [ exact RF0 | exact FRM | exact FAKE | exact RF' | exact FF | exact FBb | cbn; clear; lia | exact APF | exact FOF | exact ACF
      | exact EC | exact APE | exact FOE | exact ACE | exact E8 | exact AXS | exact MV
      | exact ST | exact CEIL | clear - LOS BSV SPA; lia
      | clear - SOB AF1; unfold AAPP_HI in *; lia | clear - PQ4 PQ3; unfold AAPP_HI in *; lia | clear - TOT0 TOT NR SZS; unfold zlength in *; lia | exact KB
      | exact MI | exact AC | exact SK ]. }
  intros msF1 mo1 KREL1 MP1 (m1 & MU1 & WM1 & MI1 & ST1 & FRM1 & FBb1 & EC1 & RF1 & AC1 & SK1 & ACE1 & ACF1 & AXS1 & MV1 & ALT).
  assert (QW1 : Forall (qwin (bv_unsigned sp + -104) ff) [(Z.shiftr ff 3 + 2147450880 + 4, Z.shiftr ff 3 + 2147450880 + 7)]%Z)
    by (apply Forall_cons; [right; cbn [fst snd]; clear; lia| apply Forall_nil]).
  pose proof (RWmF_quiet H HH _ MA LF' _ s errv (rs_ec eof) m m1 me _ (bv_unsigned sp + -104) ff fp STC0 RP0 RM0 SUBF FF RF0 HI ltac:(cbn_w; clear - FRB128; lia) MU1 WM1 MI1 QW1) as RM1.
  pose proof RM1 as RM1c. unfold RWmF in RM1. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in RM1.
  clear PC UW HOWN RDI J13 J32a J8a J32b J8b HCT FTS MV FBU EC BSC SB ERR AUX MI AC SK ATH ACP ACE SVE ACB ACF SVA FC HDR USED MB RD MRG CBH CBB PFT FI AXS.
  destruct RM1 as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HCT & FTS & MV & FBU & EC & BSC & SB & HP1 & ERR & AUX & MI & _ & _ & _ & ATH1 & ACP & ACE & SVE & ACB & ACF & SVA).
  pose proof (fun A0 k0 => qwin_hi H LF ff fp (bv_unsigned sp + -104) FF HI _ A0 k0 QW1) as DJH1. cbv beta in DJH1.
  assert (SAVED1 : rw_cells bsegs m1 (bv_unsigned sp + -104) (rs_sv s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra)) by (eapply (rw_cells_transport bsegs); [exact SAVED| exact MU1| exact WM1| apply DJH1; clear; lia]).
  assert (FR01 : rw_cells bsegs m1 (bv_unsigned sp) fr) by (eapply (rw_cells_transport bsegs); [exact FR0| exact MU1| exact WM1| apply DJH1; clear; lia]).
  clear SAVED FR0 HP RF' FAKE.
  destruct eof.
  - (* [comment removed for export] *)
    destruct CASE as [Esds K0]. subst sds k. destruct ALT as [(_ & FAKE1 & VIS1) | (KF & _)]; [| exfalso; clear - KF; discriminate].
    unfold rs_ec in EC. cbv iota in EC.
    pose proof UW as UWc. unfold PutUw in UWc. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UWc.
    destruct UWc as (FC & HDR & USED & MB & RD & MRG & CBH & CBB & PFT & FI & AXS).
    eapply (ahh_evt H HH); [exact KREL1| exact VIS1| |].
    { eapply (rs_eof H HH _ sp gp (Z_to_bv 64 ATP) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra F fc me m1 LF lo shi spa ff fp E bs fb P tot c pad7 pad2 g hw tmp gap optc ect_cells j56 j120);
        [ exact RF0 | exact FRM1 | exact SAVED1 | exact FAKE1 | exact RF1 | exact FF | exact PC | exact PCOK | exact EC
        | exact APP80 | eapply fsobj_sub; [exact FOP| clear; lia| clear; lia] | eapply accessible_sub; [exact ACP| clear; lia| unfold PARSER_SIZE; clear; lia| clear; lia] | exact P8
        | exact APE | exact FOE | exact ACE | exact SVE | exact E8 | clear - SEPPE; lia
        | exact HCT | exact AXS | exact MV
        | exact ST1 | unfold PEOF_STACK, AASSIGN_STACK; clear - LOS BSV AIS SPA; lia | exact CEIL
        | clear - SOB AF1; unfold AAPP_HI in *; lia | clear - TOT0 TOT NR SZS; unfold zlength in *; lia | clear - T4; lia | clear - T3; unfold AAPP_HI in *; lia
        | exact RA | exact SP16 | exact SPHI | exact MI | exact AC1 | exact SK1 ]. }
    intros msF2 mo2 KREL2 MP2 (m2 & MU2 & WM2 & MI2 & PC2 & EC2 & HC2 & AXS2 & AC2 & SK2 & (y0 & y1 & y2 & a0' & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & EMS & _ & MU3 & WM3 & MI3 & STK3 & RF3 & AC3 & SK3)).
    unfold rs_eof_W in MU2.
    (* [comment removed for export] *)
    set (WA := [(lo, bv_unsigned sp + -104); (P, P + 80); (E, E + 24); (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z).
    set (WF := [(Z.shiftr ff 3 + 2147450880 + 4, Z.shiftr ff 3 + 2147450880 + 7); (ff, ff + 8); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 32); (fp, fp + 1)]%Z).
    assert (MU23 : munch (WA ++ WF) m1 m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; subst WA WF; unfold sub_fp; cbn [outside app fst snd]; clear; intros x Hx; tauto. }
    pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM23.
    assert (FWF : Forall (fwin H ff fp) WF).
    { subst WF. apply Forall_cons; [right; right; left; cbn [fst snd]; clear; lia|]. apply Forall_cons; [left; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [right; right; left; cbn [fst snd]; clear; lia|]. apply Forall_cons; [right; left; reflexivity| apply Forall_nil]. }
    pose proof (fun O n => fwinF_obj H HH LF ff fp FF _ me O n FWF RF0) as WFO.
    pose proof (fun O n => fwinF_obj_sh H HH LF ff fp FF _ me O n FWF RF0) as WFS.
    pose proof (fun O n x => fwinF_outside_sh H HH LF ff fp FF _ me O n x FWF RF0) as WFX.
    pose proof (fun p0 A0 k0 IN0 => fwinF_blk H HH LF ff fp FF _ me s (LBn ++ LBin) m1 p0 A0 k0 FWF RF0 HP1 IN0) as WFB.
    pose proof (fun A0 k0 => fwinF_img H LF ff fp FF _ A0 k0 FWF) as WFI.
    pose proof (fun A0 k0 => fwinF_stack H LF ff fp FF _ A0 k0 FWF) as WFH.
    cbv beta in WFO, WFS, WFX, WFB, WFI, WFH.
    assert (DJA : forall A0 n0, AG_HTTP_CAT + 64 <= A0 -> A0 + n0 <= aceil -> (A0 + n0 <= P \/ P + 80 <= A0) -> (A0 + n0 <= E \/ E + 24 <= A0) ->
              disjoint_from WF A0 n0 -> disjoint_from (WA ++ WF) A0 n0).
    { intros A0 n0 K1 K2 K3 K4 K5. apply (proj2 (disjoint_from_app _ _ _ _)). split; [| exact K5]. subst WA. cbn [disjoint_from fst snd]. clear - K1 K2 K3 K4 CEIL. repeat split; lia. }
    assert (DJI : forall A0 n0, 0 <= A0 -> A0 + n0 <= AG_HTTP_CAT -> disjoint_from (WA ++ WF) A0 n0).
    { intros A0 n0 K0 K1. apply (proj2 (disjoint_from_app _ _ _ _)). split; [| apply WFI; unfold AG_HTTP_CAT, AIMG_TOP in *; clear - K1; lia].
      subst WA. cbn [disjoint_from fst snd]. unfold AG_HTTP_CAT, AIMG_TOP in *. clear - K1 CEIL AF1 PQ1 R1. repeat split; lia. }
    assert (DJH : forall A0 n0, bv_unsigned sp + -104 <= A0 -> disjoint_from (WA ++ WF) A0 n0).
    { intros A0 n0 K1. apply (proj2 (disjoint_from_app _ _ _ _)). split; [| apply WFH; clear - K1 HI; lia].
      subst WA. cbn [disjoint_from fst snd]. unfold AG_HTTP_CAT in *. clear - K1 CEIL LOS BSV AF1 PQ2 R2. repeat split; lia. }
    assert (DJSA : forall A0 n0, 0 <= A0 -> 0 <= n0 -> A0 + n0 <= AAPP_HI -> disjoint_from WA (sh A0) (nsh n0)).
    { intros A0 n0 K1 K2 K3. pose proof (sh_ge_lowsh A0 K1) as SL. pose proof (sh_nsh_high A0 n0 K1 K2 K3) as SU.
      pose proof (aapp_not_shadowland _ _ APP80) as NP. pose proof (aapp_not_shadowland _ _ APE) as NE'.
      subst WA. cbn [disjoint_from fst snd]. unfold AG_HTTP_CAT, ALOWSH_LO, AHI_LO in *. clear - SL SU NP NE' CEIL AF1. repeat split; lia. }
    assert (OSHA : forall x, 0 <= x -> x + 1 <= AAPP_HI -> outside WA (sh x)).
    { intros x K1 K2. pose proof (sh_ge_lowsh x K1) as SL. pose proof (sh_nsh_high x 1 K1 ltac:(clear; lia) K2) as SU. unfold nsh in SU. change ((1 + 7) / 8) with 1 in SU.
      pose proof (aapp_not_shadowland _ _ APP80) as NP. pose proof (aapp_not_shadowland _ _ APE) as NE'.
      subst WA. cbn [outside fst snd]. unfold AG_HTTP_CAT, ALOWSH_LO, AHI_LO in *. clear - SL SU NP NE' CEIL AF1. repeat split; lia. }
    assert (OSH : forall O n x, fsobj H LF O n -> aapp O n -> 0 <= n -> O <= x < O + n -> outside (WA ++ WF) (sh x)).
    { intros O n x FO AP N0 Hx. pose proof (aapp_bounds _ _ AP N0) as (B1 & B2 & B3 & _).
      assert (OA : outside WA (sh x)) by (apply OSHA; [clear - Hx B1; unfold AIMG_TOP in B1; lia| clear - Hx B3; lia]).
      pose proof (WFX O n x FO AP N0 Hx) as OF. subst WA. cbn [outside app fst snd] in OA, OF |- *. clear - OA OF. tauto. }
    assert (DJBk : forall p0 A0 k0, In (p0, A0, k0) (LBn ++ LBin) -> disjoint_from (WA ++ WF) A0 k0 /\ disjoint_from (WA ++ WF) (sh A0) (nsh k0)).
    { intros p0 A0 k0 IN0. pose proof (ah_blocks H HH _ _ _ _ HP1 IN0) as (B1 & _ & B3 & B4 & B5 & _ & B7). cbn [blk_addr blk_size fst snd] in B1, B3, B4, B5, B7.
      destruct (WFB _ _ _ IN0) as [D1 D2]. split.
      - apply DJA; [unfold AG_HTTP_CAT, AIMG_TOP in *; clear - B4; lia| exact B5
                   | pose proof (fobj_off_block0 H HH _ _ _ _ _ _ _ _ _ _ HP1 RF0 AOP IN0) as Q; clear - Q; lia
                   | pose proof (fobj_off_block0 H HH _ _ _ _ _ _ _ _ _ _ HP1 RF0 AOE IN0) as Q; clear - Q; lia| exact D1].
      - apply (proj2 (disjoint_from_app _ _ _ _)). split; [apply DJSA; [clear - B1; lia| exact B3| clear - B5 AF1; unfold AAPP_HI; lia]| exact D2]. }
    assert (CWA : Forall (aclient_write_ok H (LBn ++ LBin)) (WA ++ WF)).
    { apply Forall_app. split; [| exact (fwinF_client H LF ff fp FF (LBn ++ LBin) _ FWF)]. subst WA.
      apply Forall_cons; [exact (proj1 (stack_window_ok' H HH _ _ _ LF lo (bv_unsigned sp + -104) HP1 CEIL))|].
      apply Forall_cons; [exact (proj1 (aobj_write_ok H HH _ _ _ _ _ _ _ HP1 RF0 AOP80))|].
      apply Forall_cons; [exact (proj1 (aobj_write_ok H HH _ _ _ _ _ _ _ HP1 RF0 AOEn))|].
      apply Forall_cons; [| apply Forall_nil]. right; left. unfold aimg_client_w, ATLS_PRIV_LO, ATP, AG_HTTP_CAT. cbn [fst snd]. right; right; right; left. clear. lia. }
    pose proof (ah_RHEAP_frame H HH _ _ _ _ _ HP1 MU23 WM23 CWA) as HP3.
    pose proof (ah_rauxv_frame H HH _ _ _ _ _ AUX MU23 WM23 CWA) as AUX3.
    pose proof (ah_thr H HH _ _ _ HP3) as ATH3.
    assert (AGP : AG_HTTP_CAT + 64 <= P) by (unfold AG_HTTP_CAT, AIMG_TOP in *; clear - PQ1; lia).
    assert (AGE : AG_HTTP_CAT + 64 <= E) by (unfold AG_HTTP_CAT, AIMG_TOP in *; clear - R1; lia).
    assert (WFP : forall a kk, P <= a -> a + kk <= P + 352 -> 0 <= kk -> disjoint_from WF a kk).
    { intros a kk K1 K2 K3. eapply disjoint_from_sub; [| exact K1| exact K2]. apply WFO; [exact FOP| exact APP0| clear; lia]. }
    (* [comment removed for export] *)
    assert (UW2 : PutUw P mb (mkPST (rs_eof_c c) S L ns ls em h u es insz (rs_eof_g c g) rdi LBn Ag) m3).
    { unfold PutUw. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A]. destruct OFFP as (OPe & OPb & OPh). destruct OFFE as (OEe & OEb & OEh).
      split.
      { eapply AFieldsC_transport_gen; [exact FC| exact MU23| exact WM23| | |].
        - apply DJA; [clear - AGP; lia| clear - PQ2; lia| right; clear; lia| clear - SEPPE; lia| apply WFP; [clear; lia| cbn; clear; lia| clear; lia]].
        - intros x Hx. apply (OSH P 352 x FOP APP0); [clear; lia| clear - Hx; lia].
        - intros e dd Ld. destruct (OWN e dd Ld) as (pa & INe & _). exact (DJBk _ _ _ INe). }
      split; [eapply (rw_cells_transport bsegs); [exact HDR| exact MU23| exact WM23| apply DJA; [unfold O_PR_HDR; clear - AGP; lia| unfold O_PR_HDR; cbn; clear - PQ2; lia| right; unfold O_PR_HDR; clear; lia| unfold O_PR_HDR; cbn; clear - SEPPE; lia| apply WFP; [unfold O_PR_HDR; clear; lia| unfold O_PR_HDR; cbn; clear; lia| clear; lia]]]|].
      split; [eapply (rw_cells_transport bsegs); [exact USED| exact MU23| exact WM23| apply DJA; [unfold O_PR_USED; clear - AGP; lia| unfold O_PR_USED; cbn; clear - PQ2; lia| right; unfold O_PR_USED; clear; lia| unfold O_PR_USED; cbn; clear - SEPPE; lia| apply WFP; [unfold O_PR_USED; clear; lia| unfold O_PR_USED; cbn; clear; lia| clear; lia]]]|].
      split.
      { eapply AMBuf_transport_gen; [exact MB| exact MU23| exact WM23| | |].
        - apply DJA; [clear - AGP; lia| clear - PQ2; lia| right; clear; lia| clear - SEPPE; lia| apply WFP; clear; lia].
        - intros x Hx. apply (OSH P 352 x FOP APP0); [clear; lia| clear - Hx; lia].
        - intros x sz IN. destruct (MOWN x sz IN) as [px INx]. exact (DJBk _ _ _ INx). }
      split; [eapply (rw_cells_transport bsegs); [exact RD| exact MU23| exact WM23| apply DJA; [clear - AGP; lia| cbn; clear - PQ2; lia| right; clear; lia| cbn; clear - SEPPE; lia| apply WFP; [clear; lia| cbn; clear; lia| clear; lia]]]|].
      split; [eapply (rw_cells_transport bsegs); [exact MRG| exact MU23| exact WM23| apply DJA; [unfold O_PR_MERGE; clear - AGP; lia| unfold O_PR_MERGE; cbn; clear - PQ2; lia| right; unfold O_PR_MERGE; clear; lia| unfold O_PR_MERGE; cbn; clear - SEPPE; lia| apply WFP; [unfold O_PR_MERGE; clear; lia| unfold O_PR_MERGE; cbn; clear; lia| clear; lia]]]|].
      split; [eapply (rw_cells_transport bsegs); [exact CBH| exact MU23| exact WM23| apply DJA; [clear - AGP; lia| cbn; clear - PQ2; lia| right; clear; lia| cbn; clear - SEPPE; lia| apply WFP; [clear; lia| cbn; clear; lia| clear; lia]]]|].
      split; [eapply (rw_cells_transport bsegs); [exact CBB| exact MU23| exact WM23| apply DJA; [clear - AGP; lia| cbn; clear - PQ2; lia| right; clear; lia| cbn; clear - SEPPE; lia| apply WFP; [clear; lia| cbn; clear; lia| clear; lia]]]|].
      split; [unfold APfTab in PFT |- *; eapply (rw_cells_transport bsegs); [exact PFT| exact MU23| exact WM23| apply DJI; [unfold APF_TABPTR; clear; lia| unfold APF_TABPTR, AG_HTTP_CAT; cbn; clear; lia]]|].
      split; [eapply FTInit_transport; [exact FI| exact MU23| apply DJI; [unfold P_A_FT_INIT; clear; lia| unfold P_A_FT_INIT, AG_HTTP_CAT; clear; lia]]|].
      eapply AXStatics2_transport; [exact AXS2| exact MU3| exact WM3|]. eapply Forall_impl; [| exact (Forall_inv_tail FWF)]. intros [l h'] Kf.
      pose proof (fwin_img H LF ff fp FF _ 0x119000 0x11340 Kf ltac:(unfold AIMG_TOP; clear; lia)) as Q. cbn [fst snd] in Q |- *. left. clear - Q. lia. }
    assert (HOWN2 : HdrOwnA (LBn ++ LBin) m3 h).
    { assert (K : forall ptr len, ASvOwn (LBn ++ LBin) m1 ptr len -> ASvOwn (LBn ++ LBin) m3 ptr len).
      { intros ptr len [Z0|(L1 & p & bsx & IN & CE & AD)]; [left; exact Z0| right]. split; [exact L1|]. exists p, bsx.
        destruct (DJBk _ _ _ IN) as [D1 D2]. split; [exact IN|]. split.
        - eapply (rw_cells_transport bsegs); [exact CE| exact MU23| exact WM23|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - L1; lia). exact D1.
        - eapply addressable_transport; [exact AD| exact MU23| exact WM23| exact D2]. }
      destruct HOWN as (O1 & O2 & O3 & O4). split; [exact (K _ _ O1)|]. split; [exact (K _ _ O2)|]. split; [exact O3| exact O4]. }
    Local Ltac trj K AGP PQ2 SEPPE MU WM DJA WFP := eapply (rw_cells_transport bsegs); [exact K| exact MU| exact WM| apply DJA; [clear - AGP; lia| cbn; clear - PQ2; lia| right; clear; lia| cbn; clear - SEPPE; lia| apply WFP; [clear; lia| cbn; clear; lia| clear; lia]]].
    assert (RDI2 : rw_cells bsegs m3 (P + 240) [C1 rdi]) by (trj RDI AGP PQ2 SEPPE MU23 WM23 DJA WFP).
    assert (J13' : rw_cells bsegs m3 (P + 243) [CB 13 j13]) by (trj J13 AGP PQ2 SEPPE MU23 WM23 DJA WFP).
    assert (J32a' : rw_cells bsegs m3 (P + 256) [CB 32 j32a]) by (trj J32a AGP PQ2 SEPPE MU23 WM23 DJA WFP).
    assert (J8a' : rw_cells bsegs m3 (P + 296) [CB 8 j8a]) by (trj J8a AGP PQ2 SEPPE MU23 WM23 DJA WFP).
    assert (J32b' : rw_cells bsegs m3 (P + 304) [CB 32 j32b]) by (trj J32b AGP PQ2 SEPPE MU23 WM23 DJA WFP).
    assert (J8b' : rw_cells bsegs m3 (P + 344) [CB 8 j8b]) by (trj J8b AGP PQ2 SEPPE MU23 WM23 DJA WFP).
    assert (FTS2 : AFieldTabZero m3 \/ FT m3).
    { eapply FTState_transport; [exact FTS| exact MU23| exact WM23|].
      apply DJA; [unfold AG_FIELD_TABLE, AG_HTTP_CAT; clear; lia| unfold AG_FIELD_TABLE; clear - AF1; lia| left; unfold AG_FIELD_TABLE, AIMG_TOP in *; clear - PQ1; lia| left; unfold AG_FIELD_TABLE, AIMG_TOP in *; clear - R1; lia| apply WFI; unfold AG_FIELD_TABLE, AIMG_TOP; clear; lia]. }
    assert (MV2 : AMiscVt48 m3).
    { unfold AMiscVt48 in MV |- *. eapply (ro_cells_transport bsegs); [exact MV| exact MU23|]. apply DJI; [unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR; clear; lia|]. unfold AW_MISC_CAT_VT48, AW_MISC_CAT_VPTR, AG_HTTP_CAT. cbn. clear. lia. }
    assert (FBU2 : AFlatBuf (LBn ++ LBin) m3 fb FB fds).
    { eapply AFlatBuf_transport; [exact FBU| exact MU23| exact WM23| | |].
      - apply DJA; [unfold AG_HTTP_CAT, AIMG_TOP in *; clear - T1; lia| unfold SZ_FB; clear - T2; lia| unfold SZ_FB; clear - SEPPF; lia| unfold SZ_FB; clear - SEPEF; lia| apply WFO; [exact FOF| exact APF| unfold SZ_FB; clear; lia]].
      - intros NE. destruct FS5 as [K|(BP & _ & BCP & BAP & pf0 & INf0)]; [exfalso; exact (NE K)|]. exact (proj1 (DJBk _ _ _ INf0)).
      - intros NE. destruct FS5 as [K|(BP & _ & BCP & BAP & pf0 & INf0)]; [exfalso; exact (NE K)|]. exact (proj2 (DJBk _ _ _ INf0)). }
    assert (BSC2 : rw_cells bsegs m3 bs (BasicStreamCells stb)) by (eapply (rw_cells_transport bsegs); [exact BSC| exact MU23| exact WM23| apply DJH; clear - FRB128; lia]).
    assert (SB2 : AStateBlock (LBn ++ LBin) m3 stb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength (@nil byte))) []).
    { destruct (DJBk _ _ _ (SUBin _ INS)) as [DS1 DS2].
      eapply AStateBlock_transport; [exact SB| exact MU23| exact WM23| exact DS1| | exact DS2|]; cbn [st_fb]; intros NEs;
        (destruct STRM as [[_ EFs]|(N1 & SA' & SE)]; [exfalso; exact (NEs EFs)|]); unfold fb_cap; rewrite SA', SE;
        destruct (INA N1) as [p9 IN9]; replace (A + N - A) with N by (clear; lia); [exact (proj1 (DJBk _ _ _ (SUBin _ IN9)))| exact (proj2 (DJBk _ _ _ (SUBin _ IN9)))]. }
    assert (ERR2 : rw_cells bsegs m3 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]).
    { rewrite EA. eapply (rw_cells_transport bsegs); [exact ERR| exact MU23| exact WM23|].
      apply DJA; [unfold AERRNO, ATP, AG_HTTP_CAT; clear; lia| unfold AERRNO, ATP; cbn; clear - AF1; lia| left; unfold AERRNO, ATP, AIMG_TOP in *; cbn; clear - PQ1; lia| left; unfold AERRNO, ATP, AIMG_TOP in *; cbn; clear - R1; lia
                 | apply WFI; unfold AERRNO, ATP, AIMG_TOP; cbn; clear; lia]. }
    assert (WFR : Forall (win_fr ff 32) (WA ++ WF)).
    { apply Forall_app. split; [| exact (fwinF_fr H LF ff fp FF _ FWF)]. subst WA.
      apply Forall_cons; [apply awin_win_fr; apply awin_stack; exact CEIL|]. apply Forall_cons; [apply awin_win_fr; eapply awin_aapp; [exact APP80| clear; lia| clear; lia]|].
      apply Forall_cons; [apply awin_win_fr; eapply awin_aapp; [exact APE| clear; lia| clear; lia]|]. apply Forall_cons; [apply awin_win_fr; exact (proj1 pwin_httpcat)| apply Forall_nil]. }
    pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOP FF ltac:(clear - PQ4; lia) ltac:(clear; lia) ltac:(clear - PQ2 AF1; unfold AAPP_HI in *; lia)) as (DPF & _). change (fsz 2) with 256 in DPF.
    pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOF FF ltac:(clear - T4; lia) ltac:(clear; lia) ltac:(clear - T2 AF1; unfold AAPP_HI in *; lia)) as (DFF & _). change (fsz 2) with 256 in DFF.
    pose proof (fsobj_windows _ HH _ _ _ _ _ _ _ RF0 FOE FF ltac:(clear - R4; lia) ltac:(clear; lia) ltac:(clear - R2 AF1; unfold AAPP_HI in *; lia)) as (DEF & _). change (fsz 2) with 256 in DEF.
    pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACP MU23 WFR F0 F8' ltac:(clear; lia) ltac:(unfold PARSER_SIZE; clear - DPF; lia)) as ACP2.
    pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACE MU23 WFR F0 F8' ltac:(clear; lia) ltac:(clear - DEF; lia)) as ACE2.
    pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACB MU23 WFR F0 F8' ltac:(clear; lia) ltac:(clear - SOB F2; lia)) as ACB2.
    pose proof (accessible_transport_fr _ _ _ _ _ ff 32 ACF MU23 WFR F0 F8' ltac:(clear; lia) ltac:(clear - DFF; lia)) as ACF2.
    pose proof (aobj_shvis H HH _ _ _ _ _ _ HP3 RF3 AOEn ltac:(clear; lia)) as SVE2.
    assert (SVA2 : 1 <= N -> shvis m3 A (A + N)) by (intros N1; destruct (INA N1) as [p9 IN9]; exact (ah_blk_shvis H HH _ _ _ _ _ _ HP3 (SUBin _ IN9))).
    assert (FR0' : rw_cells bsegs m3 (bv_unsigned sp) fr) by (eapply (rw_cells_transport bsegs); [exact FR01| exact MU23| exact WM23| apply DJH; clear; lia]).
    (* [comment removed for export] *)
    assert (XP2 : xpres H LBin SP (hread_X P E fb stb [] [] ++ XS) m0 m3).
    { eapply xpres_trans; [exact XP0|]. eapply xpres_trans.
      - eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP1| exact MU1| exact WM1|] | clear; lia| exact SUBin| intros a K; exact K].
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
      - eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP1| exact MU23| exact WM23|] | clear; lia| exact SUBin| intros a K; exact K].
        subst WA WF. repeat apply Forall_cons; [| | | | | | | | apply Forall_nil]; cbn [fst snd].
        + left. clear - CEIL SPC. lia.
        + right. intros a Ha. unfold hread_X, put_X. cbn. do 2 right. left. clear - Ha. lia.
        + right. intros a Ha. unfold hread_X, put_X. cbn. do 3 right. left. exact Ha.
        + right. intros a Ha. unfold hread_X, put_X. cbn. do 4 right. left. exact Ha.
        + right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
        + right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
        + right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
        + right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia. }
    (* [comment removed for export] *)
    left. unfold rs_done. cbn [cfg_ms cfg_model]. cbn_w.
    pose proof (RWp_eof_post _ MA _ RP0) as RP'. unfold w_after_eof, pst_eof in RP'. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in RP'.
    pose proof (rs_eof_facts c g PCOK) as (PCOK' & EOK' & EOUT' & _).
    exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, y3, y4, y5, y6, m3, (mkW (mkPST (rs_eof_c c) S L ns ls em h u es insz (rs_eof_g c g) rdi LBn Ag) PB FBB FB fds Fs [] nr), s, errv, (rs_eof_E c), tot, XS.
    cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
    split; [exact EMS|]. split; [exact KREL2|]. split; [exact (ah_mpres_trans H HH _ _ _ MP (ah_mpres_trans H HH _ _ _ MP1 MP2))|].
    pose proof (fsobj_sub _ _ _ _ P 80 FOP ltac:(clear; lia) ltac:(clear; lia)) as FOP80.
    pose proof (fun O n => fwinF_obj H HH LF ff fp FF _ me O n (Forall_inv_tail FWF) RF0) as WFO3. cbv beta in WFO3.
    assert (PC3 : rw_cells bsegs m3 P (ParserCoreCells (rs_eof_c c) pad7 pad2)).
    { eapply (rw_cells_transport bsegs); [exact PC2| exact MU3| exact WM3|]. change (Z.of_nat (cells_size (ParserCoreCells (rs_eof_c c) pad7 pad2))) with 80.
      apply WFO3; [exact FOP80| exact APP80| clear; lia]. }
    assert (EC3 : rw_cells bsegs m3 E (ErrCodeCells (rs_eof_E c))).
    { eapply (rw_cells_transport bsegs); [exact EC2| exact MU3| exact WM3|]. change (Z.of_nat (cells_size (ErrCodeCells (rs_eof_E c)))) with 24.
      apply WFO3; [exact FOE| exact APE| clear; lia]. }
    assert (HC3 : AHttpCat m3 (rs_eof_g c g)).
    { eapply AHttpCat_transport; [exact HC2| exact MU3| exact WM3| |]; apply (fwinF_img H LF ff fp FF _ _ _ (Forall_inv_tail FWF)); unfold AG_HTTP_CAT, AG_HTTP_CAT_GUARD, AIMG_TOP; clear; lia. }
    assert (AXS3 : AXStatics2 m3) by (destruct UW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K); exact K).
    split.
    { (* [comment removed for export] *) unfold RWm. cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
      split; [exact PC3|]. split; [exact UW2|]. split; [exact HOWN2|]. split; [exact RDI2|].
      split; [exact J13'|]. split; [exact J32a'|]. split; [exact J8a'|]. split; [exact J32b'|]. split; [exact J8b'|].
      split; [exact HC3|]. split; [exact FTS2|]. split; [exact MV2|]. split; [exact FBU2|]. split; [exact EC3|]. split; [exact BSC2|].
      split; [exact SB2|]. split; [exact HP3|]. split; [exact ERR2|]. split; [exact AUX3|]. split; [exact MI3|].
      split; [exact RF3|]. split; [exact AC3|]. split; [exact SK3|]. split; [exact ATH3|].
      split; [exact ACP2|]. split; [exact ACE2|]. split; [exact SVE2|]. split; [exact ACB2|]. split; [exact ACF2| exact SVA2]. }
    split; [exact RP'|]. split; [exact ALK|]. split; [exact STK3|]. split; [exact FR0'|]. split; [exact FXS|]. split; [exact XP2|].
    split; [exact TOT0|]. split; [exact TOT|]. split; [exact EOK'|].
    split; [destruct EOUT' as [[K _] | [K _]]; [right; exact K | left; exact K]|].
    split; [exact WM0|].
    intros ECL NS. exfalso. destruct EOUT' as [[K _] | [_ K]]; [| exact (NS K)].
    rewrite ECL in K. clear - K. unfold http_fail, EC_clear in K. cbn in K. lia.
  - (* [comment removed for export] *)
    destruct CASE as (K1 & KS & IO & WM1' & NRB). destruct ALT as [(KF & _) | (_ & FAKE1 & a0' & a1' & VIS1)]; [exfalso; clear - KF; discriminate|].
    unfold rs_ec in EC. cbv iota in EC.
    pose proof (proj1 FBU) as FBC1.
    eapply (ahh_evt H HH); [exact KREL1| exact VIS1| |].
    { eapply (rs_parse _ sp gp (Z_to_bv 64 ATP) t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 (wz k) (wz (E + 16)) t3 t4 t5 t6 F fc m1 lo spa ff E bs fb P tot FB _ tmp gap);
        [ exact FRM1 | exact FBC1 | exact FB8 | exact APF | exact ACF
        | exact B0 | exact BIO | clear - BOLE; lia | exact BCE
        | clear - PQ4 PQ3; unfold AAPP_HI in *; lia | clear - TOT0 TOT NR SZS; unfold zlength in *; lia | clear - R4 R3; unfold AAPP_HI in *; lia
        | exact F0 | clear - F2 AF1; lia
        | clear - LOS BSV; lia | exact CEIL | exact MI ]. }
    intros msF2 mo2 KREL2 MP2 (m2 & jj & EMS & MU2 & WM2 & MI2 & FRM2).
    assert (QW2 : Forall (qwin (bv_unsigned sp + -104) ff) [(spa + 128, spa + 152)]%Z) by (apply Forall_cons; [left; cbn [fst snd]; clear - SPACE SPA; lia| apply Forall_nil]).
    pose proof (RWmF_quiet H HH _ MA LF' _ s errv EC_clear m1 m2 me _ (bv_unsigned sp + -104) ff fp STC0 RP0 RM1c SUBF FF RF0 HI ltac:(cbn_w; clear - FRB128; lia) MU2 WM2 MI2 QW2) as RM2.
    pose proof (fun A0 k0 => qwin_hi H LF ff fp (bv_unsigned sp + -104) FF HI _ A0 k0 QW2) as DJH2. cbv beta in DJH2.
    assert (DJl : forall A0 n0, A0 + n0 <= aceil -> disjoint_from [(spa + 128, spa + 152)]%Z A0 n0) by (intros A0 n0 K; cbn; split; [left; clear - K SPACE; lia| exact I]).
    assert (SAVED2 : rw_cells bsegs m2 (bv_unsigned sp + -104) (rs_sv s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra)) by (eapply (rw_cells_transport bsegs); [exact SAVED1| exact MU2| exact WM2| apply DJH2; clear; lia]).
    assert (FR02 : rw_cells bsegs m2 (bv_unsigned sp) fr) by (eapply (rw_cells_transport bsegs); [exact FR01| exact MU2| exact WM2| apply DJH2; clear; lia]).
    assert (ST2 : stk bsegs m2 lo spa) by (eapply (stk_transport bsegs); [exact ST1| exact MU2| exact WM2| intros x Hx; left; cbn; clear - Hx; lia]).
    pose proof FAKE1 as (HDR1 & OPTC1 & OSZ & J561 & ECTC1 & ESZ & J1201 & FPW1 & SHU1 & FL1).
    Local Ltac trl K DJl := eapply (rw_cells_transport bsegs); [exact K| eassumption| eassumption| apply DJl].
    assert (FAKE2 : rs_fake m2 ff fp hw optc j56 ect_cells j120 248 248).
    { split; [trl HDR1 DJl; cbn [cells_size csize Nat.add]; clear - F2; lia|]. split; [trl OPTC1 DJl; rewrite OSZ; clear - F2; lia|]. split; [exact OSZ|].
      split; [trl J561 DJl; cbn [cells_size csize Nat.add]; clear - F2; lia|]. split; [trl ECTC1 DJl; rewrite ESZ; clear - F2; lia|]. split; [exact ESZ|].
      split; [trl J1201 DJl; cbn [cells_size csize Nat.add]; clear - F2; lia|]. split; [trl FPW1 DJl; cbn [cells_size csize Nat.add]; clear - F2; lia|].
      split; [trl SHU1 DJl; unfold rs_shcells; cbn [cells_size csize Nat.add length repeat]; rewrite SHFF; clear - SF1 SA; lia|].
      trl FL1 DJl. cbn [cells_size csize Nat.add]. clear - F5 F2. lia. }
    assert (XP2 : xpres H LBin SP (hread_X P E fb stb [] [] ++ XS) m0 m2).
    { eapply xpres_trans; [exact XP0|]. eapply xpres_trans.
      - eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP1| exact MU1| exact WM1|] | clear; lia| exact SUBin| intros a K; exact K].
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. intros a Ha. apply rin_ivs_app. right. apply FRX. clear - Ha. lia.
      - eapply xpres_weaken; [eapply (xpres_of_munch H) with (SP := SP); [exact HH| exact HP1| exact MU2| exact WM2|] | clear; lia| exact SUBin| intros a K; exact K].
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. clear - SPACE SPA SPC. lia. }
    right. exists (wM N (mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr)), (mkW (mkPST c S L ns ls em h u es insz g rdi LBn Ag) PB FBB FB fds Fs sds nr).
    split; [exact WM1'|].
    unfold rs_at_put, rs_core, rs_frames. cbn [cfg_ms cfg_model]. cbn_w. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
    exists t0, t1, t2, a4, a5, a6, a7, (wz k), (wz (E + 16)), t3, t4, t5, t6, m2, s, errv, EC_clear, tot, spa, ff, fp,
           (C8 (wz (Z.shiftr (E + 16) 3 + 2147450880))), [C8 (wz (fb_in FB)); C8 (wz (fb_size FB)); CB 8 jj], gap, hw, optc, j56, ect_cells, j120, XS.
    split; [exact EMS|]. split; [clear - K1 KS; lia|]. split; [exact NS11|]. split; [exact KREL2|].
    split; [exact (ah_mpres_trans H HH _ _ _ MP (ah_mpres_trans H HH _ _ _ MP1 MP2))|].
    split; [| clear; lia].
    split; [exact RM2|]. split; [exact RP0|]. split; [exact ALK|]. split; [exact ST2|].
    split; [split; [exact FRM2| split; [exact SAVED2| split; [exact FR02| split; [exact SZFR| exact FAKE2]]]]|].
    split; [exact FF|]. split; [exists me; exact RF0|].
    split; [exact FXS|]. split; [exact FRX|]. split; [exact XP2|]. split; [exact TOT0|]. split; [exact TOT|]. exact NRB.
Qed.
End HCW.
