(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_ListFind H_UpnpPrintf H2Kit AWUb.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import H_germ_seg1 H_germ_seg3 H_germ_seg4.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (P lo q kq kP : Z) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).

Variables (meth rm sc isreq maj min A len cap cur csz : Z) (canary : word).

Variables (first last size flh fk ffree : Z) (hvs : list hv).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - GERM_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^64.
Hypothesis Q63 : q < 2^63.
Hypothesis Q47 : q <= 2^47 - 64.
Hypothesis SHZ : shz m0 (sh lo) (sh q).
Hypothesis SHR : shr m0 (sh lo - sh lo mod 8) (sh q + 8).
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 2.
Hypothesis FE0 : FSENV FI m0.

Local Notation F := (germF FI st).  Local Notation FL := (germFL FI st).  Local Notation SF := (germSF FI st).  Let st1 := fs_next FI st 3.

Notation WPg := [(P + 384, P + 400); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)]%Z.

Notation W0c VWc := ((lo, q) :: FSIV (WPg ++ VWc))%Z.

Notation gshadow w1 w2 w3 :=
  ([C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
   C1 (Z_to_bv 8 w1); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
   C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2);
   C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2);
   C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
   C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3);
   C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3);
   C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).

Hypothesis PAL : P = 8 * kP.
Hypothesis PLO : 0x609000 <= P.
Hypothesis PHI : P + 504 <= alloc_ceiling.
Hypothesis SHWP : shw m0 P 504.
Hypothesis SHWCH : shw m0 A0_CHUNKED 8.
Hypothesis SHWERR : shw m0 ERRNO_G 4.
Hypothesis TPV : tp = Z_to_bv 64 6190512.
Hypothesis CURR : 0 <= cur <= len.
Hypothesis METHR : 0 <= meth <= 11.
Hypothesis RMR : 0 <= rm <= 11.
Hypothesis SCR : - 2^31 <= sc < 2^31.
Hypothesis ISR : 0 <= isreq <= 1.
Hypothesis ARNG : 0 <= A /\ A + cur < 2^64.
Hypothesis ANZ : 0 < cur -> 0 < A.

Notation GSTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 SF) (Z_to_bv 64 F) x20 x21 x22 (Z_to_bv 64 F) (Z_to_bv 64 2147450880) x25 s10 s11
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Local Notation minvG := (H_germ_seg1.minvG FI P lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0).
Local Notation plbG := (H_germ_seg1.plbG FI P st).
Local Notation pinvG := (H_germ_seg1.pinvG P meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree).
Local Notation hview := (H_germ_seg1.hview P first hvs).
Local Notation hreg := (H_germ_seg1.hreg FI).
Local Notation hpure := (H_germ_seg1.hpure FI).
Local Notation vwc_ok := (H_germ_seg1.vwc_ok hvs).
Local Notation WEG := (H_germ_seg1.WEG FI lo q st).
Local Notation rframeG := (H_germ_seg1.rframeG FI lo q st).
Local Notation postG := (H_germ_seg1.postG FI P lo q st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0).
Local Notation hsafeW := (H_germ_seg1.hsafeW FI).
Local Notation hsafe_iv := (H_germ_seg1.hsafe_iv FI).
Local Notation vw_ok := (H_germ_seg1.vw_ok hvs).
Local Notation vw_ok_nil := (H_germ_seg1.vw_ok_nil hvs).

Local Notation sub_fp_WPg := (H_germ_seg3.sub_fp_WPg FI P lo q).

Local Notation blockCf_stmt := (H_germ_seg4.blockCf_stmt FI P lo q st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs).

Hypothesis PLB : plbG.
Local Notation PLBv := (PLB : lb (fs_live FI st) P 504).
Hypothesis HPURE : forall h, In h hvs -> hpure h.

Hypothesis HAPART : forall h h', In h hvs -> In h' hvs ->
  (hvN h' + 24 <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvN h') /\ (hvIt h' + 88 <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvIt h')
  /\ ((hvA h = hvA h' /\ hvLen h = hvLen h' /\ hvCap h = hvCap h') \/ ru8G (hvA h' + (hvCap h' + 1)) <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvA h').
Hypothesis HV0 : hview m0.

Hypothesis FEV : forall m, munch (W0c (hvW hvs)) m0 m -> wmono asegs m0 m -> FSENV FI m.

Local Notation geomG := (H_germ_seg1.geomG FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation WPg_app := (H_germ_seg1.WPg_app P lo m0 A cur SHWP ARNG).
Local Notation WPg_out := (H_germ_seg1.WPg_out FI P lo m0 A cur SHWP ARNG).
Local Notation shwP_now := (H_germ_seg1.shwP_now FI P lo st m0 A cur RF0 SHWP ARNG PLB).
Local Notation liveG := (H_germ_seg1.liveG FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_cons2 := (H_germ_seg1.sub_fp_cons2 meth rm sc isreq A len cur CURR METHR RMR SCR ISR ARNG).
Local Notation sub_fp_stk := (H_germ_seg1.sub_fp_stk FI P lo q A cur ARNG).
Local Notation sub_fp_F := (H_germ_seg1.sub_fp_F FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_SF := (H_germ_seg1.sub_fp_SF FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_ent := (H_germ_seg1.sub_fp_ent FI P lo q A cur ARNG).
Local Notation sub_fp_ctl := (H_germ_seg1.sub_fp_ctl FI P lo q A cur ARNG).
Local Notation sub_fp_errno := (H_germ_seg1.sub_fp_errno FI P lo q A cur ARNG).
Local Notation prologueG := (H_germ_seg1.prologueG FI STACK_MALLOC_3 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 QHI Q47 RF0 FCO FE0 ARNG PLB).
Local Notation sub_fp_WEG := (H_germ_seg1.sub_fp_WEG FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation exitG := (H_germ_seg1.exitG FI SET_SHADOW_F5 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 Q47 RF0 ARNG PLB).
Local Notation blockA := (H_germ_seg1.blockA FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree CLO LO AL16 RF0 PAL PLO PHI SHWP CURR METHR RMR SCR ISR ARNG ANZ PLB).
Local Notation hview_frame := (H_germ_seg1.hview_frame FI P lo A cur first hvs ARNG HPURE).
Local Notation hsafe_of := (H_germ_seg1.hsafe_of FI lo A cur ARNG).
Local Notation hsafe_W0 := (H_germ_seg1.hsafe_W0 FI P lo q st m0 A cur CLO RF0 ARNG PLB).
Local Notation hview_now0 := (H_germ_seg1.hview_now0 FI P lo q st m0 A cur first hvs CLO RF0 ARNG PLB HPURE HV0).
Local Notation W0c_fsw := (H_germ_seg1.W0c_fsw FI P lo q st m0 A cur hvs CLO RF0 ARNG PLB HPURE).

Local Notation pinvG_frame := (H_germ_seg3.pinvG_frame P lo meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree ARNG).
Local Notation pinv_dj_F := (H_germ_seg3.pinv_dj_F FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation pinv_dj_SF := (H_germ_seg3.pinv_dj_SF FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation pinv_dj_stk := (H_germ_seg3.pinv_dj_stk P lo CLO PHI).
Local Notation shwE_now := (H_germ_seg3.shwE_now FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation blockDf := (H_germ_seg3.blockDf FI IC P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs CLO LO AL16 Q63 RF0 PAL PLO PHI SHWP SHWERR TPV ARNG PLB HPURE).

Local Notation le1_smallG := (H_germ_seg4.le1_smallG lo A cur ARNG).
Local Notation to_lower_nzG := (H_germ_seg4.to_lower_nzG lo A cur ARNG).
Local Notation te_loopB := (H_germ_seg4.te_loopB FI IC lo gp tp s10 s11 F_ fc A cur hvs ARNG HPURE).
Local Notation rfsB := (H_germ_seg4.rfsB FI IC lo q kq st gp tp s10 s11 F_ fc A cur canary hvs CLO LO AL16 QHI Q47 ARNG HPURE).
Local Notation shwStk_nowG := (H_germ_seg4.shwStk_nowG FI P lo q kq st m0 A cur hvs CLO LO AL16 Q47 SHZ SHR RF0 ARNG PLB HPURE).
Local Notation sub_fp_vw := (H_germ_seg4.sub_fp_vw FI P lo q A cur hvs ARNG).
Local Notation vw_ok_1 := (H_germ_seg4.vw_ok_1 lo A cur hvs ARNG).
Local Notation hview_upd := (H_germ_seg4.hview_upd FI P lo A cur first hvs ARNG HPURE).

Ltac mv_tacG := unfold H_germ_seg1.minvG; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Ltac pv_tacG := unfold H_germ_seg1.pinvG; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption| eassumption].

Ltac shwP_here SHWPs MU0 N :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    first [ lazymatch goal with H : shw mm P 504 |- _ => idtac end
          | (try clear N); assert (N : shw mm P 504) by (eapply (shw_frame WPg); [exact SHWPs| exact MU0| exact WPg_app]) ] end.

Ltac wPA SHWPs MU0 N pc :=
  repeat first [ (is_ms; tryif at_pc pc then fail else (shwP_here SHWPs MU0 N; cstep)) | (is_if; br_auto) ].

Ltac wPAU SHWPs MU0 N pc :=
  repeat first [ (is_ms; tryif at_pc pc then fail else (shwP_here SHWPs MU0 N; cstep)) | (has_b2z_if; ub_b2z; lit_branch_safe) | (is_if; first [ br_auto | ubr2 | ubr3 ]) ].

#[using="IC STACK_MALLOC_2 kq kP CLO LO AL16 QHI Q47 SHZ SHR RF0 FCO PAL PLO PHI SHWP SHWCH ARNG PLB HPURE HAPART FEV"] Lemma blockCf : blockCf_stmt.
Proof.
  unfold blockCf_stmt. intros until x31. intros Hh INV PINV HV Q Kc Kn.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  unfold mbuf_cells in PMB. unfold llist_cells in PL.
  pose proof HV as (LS & HI). destruct (HI h Hh) as ((N1 & N2 & N3 & SHN) & (I1 & I2 & I3 & SHI) & VC & SHV & (vbs & VB & VN) & (sl & SL & SE0)).
  destruct (ru8G_spec (hvA h + (hvCap h + 1))) as (RU1 & kE & RU2).
  assert (SE : hvA h + (hvCap h + 1) + Z.of_nat (length sl) = 8 * kE) by (rewrite SE0; exact RU2).
  assert (SLL : Z.of_nat (length sl) <= 8) by (clear - SE0 RU1; lia).
  clear SE0 RU2.
  destruct (HPURE h Hh) as (LC & CAPB & RN & RI & RV). unfold H_germ_seg1.hreg in RN, RI, RV.
  destruct (lsegA_node _ _ _ _ _ (hvN h) (hvIt h) (hvId h) LS ltac:(apply in_map_iff; exists h; split; [reflexivity| exact Hh])) as (pv' & nx & NC).
  unfold node_cells in NC. unfold mbuf_cells in VC.
  pose proof AE as AEs.
  pose proof (shwStk_nowG m (q' + 24) 16 MU ltac:(clear - LO Hq; lia) ltac:(clear - Hq; lia) ltac:(lia)) as SHMm.
  assert (SHCm : shw m A0_CHUNKED 8) by (eapply (shw_frame_fs FI (W0c []) m0 m); [exact SHWCH| exact MU| exact (W0c_fsw [] vw_ok_nil)| left; unfold A0_CHUNKED; clear - FSB1; lia]).
  hideW MU WM.
  pose proof (munch_refl [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  assert (FSWC : Forall (fsw_iv FI) [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z).
  { apply Forall_cons; [left; apply app_iv_stack; exact CLO|]. apply Forall_cons; [right; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PFS1 PFS2 FSB1 FSB2 FSB5; lia|].
    apply Forall_cons; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - RV; lia| apply Forall_nil]. }
  step. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ RN ACR. lia. } clear KZ.
  walk_ub_to 0x898c8.
  cstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHI1 : shw mm (hvIt h) 88) by (eapply (shw_frame_fs FI _ m mm); [exact SHI| exact MU0| exact FSWC| clear - RI; lia]) end.
  walk_ub_to 0x898e8. clear SHI1.

  clear N1 N2 N3 I1 I2 I3 RN RI SHN SHI. try clear NC. try clear VC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 11 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  step. step. step.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  assert (SHVc : shw mc (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m mc); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
  assert (SHMc : shw mc (q' + 24) 16) by (eapply (shw_frame_fs FI _ m mc); [exact SHMm| exact MU0| exact FSWC| right; clear - CLO LO Hq FSB2; lia]).
  assert (SHCc : shw mc A0_CHUNKED 8) by (eapply (shw_frame_fs FI _ m mc); [exact SHCm| exact MU0| exact FSWC| left; unfold A0_CHUNKED; clear - FSB1; lia]).
  env_sync AE MU0 WM0.
  split_chunk QC 2%nat QCa MPC.
  eapply (rfsB h vbs sl kE 0x89924 q' kq');
    [ exact Hh | exact Hq | exact Hq32 | apply ret_pc_even; [lia| reflexivity] | exact ST | eassumption | exact AE | exact MPC | exact VB | exact VN
    | exact SL | exact SE | exact SLL | exact SHVc | exact SHMc | exact SHCc | exact PGOT | exact PCAN | ].
  intros m' vbs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MUc WMc MI' ST' AE' MPC' VB' VN' PGOT' PCAN'.
  clear VB VN MPC ST AE PGOT PCAN SHVc SHMc SHCc. try clear MI.
  transport_after_call asegs mc m' MUc WMc. clear MUc WMc.
  join_chunks QCa MPC' QC.
  rename m' into mR.
  assert (HS3 : hsafeW [(lo, q); (SF, SF + 64); (P + 440, P + 480)]%Z).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [left; cbn [fst]; exact CLO|].
    apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia| apply Forall_nil]. }
  assert (DJ4 : forall X n n', hreg X n -> 0 <= n' <= ru8G (X + n) - X -> (X + n' <= hvA h \/ hvA h + (hvCap h + 1) <= X) ->
           disjoint_from [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z X n').
  { intros X n n' HR Hn' D4. pose proof (proj2 HS3 X n HR) as D3. cbn [disjoint_from] in D3 |- *. destruct D3 as (D1 & D2 & D3 & _).
    split; [clear - D1 Hn'; lia|]. split; [clear - D2 Hn'; lia|]. split; [clear - D3 Hn'; lia|]. split; [exact D4| exact I]. }
  assert (HV3 : hview mR).
  { eapply (hview_upd h _ m mR Hh HV MU0 WM0 FSWC).
    - intros h' Hh'. destruct (HPURE h' Hh') as (_ & _ & RN' & RI' & _). destruct (HAPART h h' Hh Hh') as (A1 & A2 & _).
      pose proof (ru8G_spec (hvN h' + 24)) as (U1 & _). pose proof (ru8G_spec (hvIt h' + 88)) as (U2 & _).
      split; [apply (DJ4 _ 24 24 RN'); [clear - U1; lia| clear - A1 RU1; lia] | apply (DJ4 _ 88 88 RI'); [clear - U2; lia| clear - A2 RU1; lia]].
    - intros h' Hh'. destruct (HPURE h' Hh') as (LC' & _ & _ & _ & RV'). destruct (HAPART h h' Hh Hh') as (_ & _ & [(E1 & E2 & E3)|A3]); [left; repeat split; symmetry; assumption| right].
      pose proof (ru8G_spec (hvA h' + (hvCap h' + 1))) as (U3 & _).
      apply (DJ4 _ (hvCap h' + 1) (ru8G (hvA h' + (hvCap h' + 1)) - hvA h') RV'); [clear - LC' U3; lia| clear - A3 RU1 U3; lia].
    - assert (RVh : hreg (hvA h) (hvCap h + 1)) by exact RV.
      pose proof (proj2 HS3 _ _ RVh) as D3. cbn [disjoint_from] in D3 |- *. destruct D3 as (D1 & D2 & D3 & _).
      split; [clear - D1 LC; lia|]. split; [clear - D2 LC; lia|]. split; [clear - D3 LC; lia|]. split; [right; lia| exact I].
    - exists vbs'. split; [exact VB'| exact VN']. }
  assert (SUB01 : sub_fp (W0c []) (W0c (VW1 h))).
  { intros xo Ho. cbn [outside app VW1] in *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat (split; [assumption|]). exact I. }
  assert (SUBC : sub_fp [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z (W0c (VW1 h))).
  { intros xo Ho. cbn [outside app VW1] in *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
    split; [exact H1|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [exact H5|]. split; [exact H7| exact I]. }
  assert (MUw : hid2 (munch (W0c (VW1 h)) m0 m)) by exact (munch_weaken (W0c []) (W0c (VW1 h)) m0 m SUB01 MU).
  clear MU. rename MUw into MU.
  absorbW MU WM MU0 WM0 SUBC.
  clear AEs. rename AE' into AEs. fs_sync FI RF MU0 WM0 FK LSUB.
  step.   if_cases K0.
  {
    clear K0. eapply (Kn mR); [mv_tacG | pv_tacG | exact HV3]. }
  clear K0.

  pose proof (shwP_now mR FK) as SHWPs.
  pose proof (munch_refl WPg mR) as MU0. pose proof (wmono_refl asegs mR) as WM0.
  hideW MU WM.
  wPA SHWPs MU0 SHWPn 0x89960.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mP end.
  assert (HSP : hsafeW WPg).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|]. apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia| apply Forall_nil]. }
  pose proof (hview_frame _ mR mP HV3 MU0 WM0 HSP) as HVP.
  pose proof (sub_fp_WPg (VW1 h)) as SUBW.
  absorbW MU WM MU0 WM0 SUBW. env_sync AEs MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  pose proof (FEV mP (munch_weaken _ _ m0 mP (sub_fp_vw (VW1 h) (vw_ok_1 h Hh)) MU) WM) as FEP.
  hideW MU WM.
  step.
  eapply evt_cut.
  { eapply (UpnpPrintf_spec_A FI STACK_MALLOC_2) with (lo := lo) (st := stc);
      [ exact PIWC | exact ST' | exact CLO | unfold A0_RT_STACK; clear - LO Hq; lia | clear - Hq32; Z.div_mod_to_equations; lia | clear - Hq QHI; lia
      | exact MI' | exact AEs | exact RF | exact (fs_call_ok_push FI st stc tp 1%nat _ FCO LIVE1) | exact FEP ]. }
  intros msU POU. unfold UpnpPrintf_post_A in POU.
  destruct POU as (g5 & g6 & g7 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & mU & stU & -> & MUc & WMc & MIU & FKc & LIVEc & RFU & STU & AEU & PIWCU).
  replace (ret_pc (Z_to_bv 64 563556)) with (Z_to_bv 64 563556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  fk_move LE FKc WMc. fk_move LJ1 FKc WMc. fk_move LK2 FKc WMc. fk_move LR2 FKc WMc. fk_move LK1 FKc WMc. fk_move LR1 FKc WMc.
  fk_move FH FKc WMc. fk_move FT FKc WMc. fk_move SHF FKc WMc. fk_move FLG FKc WMc.
  fk_move PM FKc WMc. fk_move PRS FKc WMc. fk_move PV FKc WMc. fk_move PL FKc WMc. fk_move PE FKc WMc. fk_move PMB FKc WMc. fk_move PC FKc WMc. fk_move PS FKc WMc.
  clear ST' AEs MI' RF PIWC SHWPs SHWPn FEP.
  transport_after_call asegs mP mU MUc WMc.
  assert (FK' : fkeep FI WPg st m0 mU).
  { eapply (fkeep_trans FI WPg st m0 mP mU FK). eapply (fkeep_weaken FI [] WPg stc st mP mU FKc); [sub_fp_solve| exact LSUB]. }
  clear FK FKc; rename FK' into FK.
  assert (HSU : hsafeW ((lo, q') :: FSIV [])%Z).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [left; cbn [fst]; exact CLO|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear; lia|]. apply Forall_cons; [right; right; left; cbn [fst snd]; clear; lia| apply Forall_nil]. }
  pose proof (hview_frame _ mP mU HVP MUc WMc HSU) as HVU.
  assert (SUBU : sub_fp ((lo, q') :: FSIV [])%Z (W0c (VW1 h))).
  { intros xo Ho. cbn [outside app] in *. destruct Ho as (H1 & H2 & H3 & _). split; [clear - H1 Hq; lia|]. split; [exact H2|]. split; [exact H3| exact I]. }
  absorbW MU WM MUc WMc SUBU. clear MUc WMc.
  step. step. step.
  rewrite LIVE1 in LIVEc.
  eapply (Kc mU); [mv_tacG | pv_tacG | exact HVU].
Qed.

End W.
