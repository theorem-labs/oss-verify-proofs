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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_ListFind H_UpnpPrintf H2Kit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import H_germ_seg1 H_germ_seg2 H_germ_seg3 H_germ_seg4 H_germ_seg5.

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
Hypothesis TPV : tp = Z_to_bv 64 6187376.
Hypothesis CURR : 0 <= cur <= len.
Hypothesis METHR : 0 <= meth <= 11.
Hypothesis RMR : 0 <= rm <= 11.
Hypothesis SCR : - 2^31 <= sc < 2^31.
Hypothesis ISR : 0 <= isreq <= 1.
Hypothesis ARNG : 0 <= A /\ A + cur < 2^64.

Notation GSTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 F) (Z_to_bv 64 SF) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 F) (Z_to_bv 64 2147450880)
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Local Notation minvG := (H_germ_seg1.minvG FI P lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
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

Local Notation geomG := (H_germ_seg1.geomG FI P st m0 A cur RF0 ARNG PLB).
Local Notation WPg_app := (H_germ_seg1.WPg_app P m0 A cur SHWP ARNG).
Local Notation WPg_out := (H_germ_seg1.WPg_out FI P m0 A cur SHWP ARNG).
Local Notation shwP_now := (H_germ_seg1.shwP_now FI P st m0 A cur RF0 SHWP ARNG PLB).
Local Notation liveG := (H_germ_seg1.liveG FI P st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_cons2 := (H_germ_seg1.sub_fp_cons2 meth rm sc isreq A len cur CURR METHR RMR SCR ISR ARNG).
Local Notation sub_fp_stk := (H_germ_seg1.sub_fp_stk FI P lo q A cur ARNG).
Local Notation sub_fp_F := (H_germ_seg1.sub_fp_F FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_SF := (H_germ_seg1.sub_fp_SF FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_ent := (H_germ_seg1.sub_fp_ent FI P lo q A cur ARNG).
Local Notation sub_fp_ctl := (H_germ_seg1.sub_fp_ctl FI P lo q A cur ARNG).
Local Notation sub_fp_errno := (H_germ_seg1.sub_fp_errno FI P lo q A cur ARNG).
Local Notation prologueG := (H_germ_seg1.prologueG FI STACK_MALLOC_3 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 QHI Q63 RF0 FCO FE0 PLO PHI SHWP ARNG PLB).
Local Notation sub_fp_WEG := (H_germ_seg1.sub_fp_WEG FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation exitG := (H_germ_seg1.exitG FI SET_SHADOW_F5 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 Q63 RF0 ARNG PLB).
Local Notation blockA := (H_germ_seg1.blockA FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree CLO LO AL16 RF0 PAL PLO PHI SHWP METHR RMR SCR ISR ARNG PLB).
Local Notation hview_frame := (H_germ_seg1.hview_frame FI P A cur first hvs ARNG HPURE).
Local Notation hsafe_of := (H_germ_seg1.hsafe_of FI A cur ARNG).
Local Notation hsafe_W0 := (H_germ_seg1.hsafe_W0 FI P lo q st m0 A cur CLO RF0 ARNG PLB).
Local Notation hview_now0 := (H_germ_seg1.hview_now0 FI P lo q st m0 A cur first hvs CLO RF0 ARNG PLB HPURE HV0).
Local Notation W0c_fsw := (H_germ_seg1.W0c_fsw FI P lo q st m0 A cur hvs CLO RF0 ARNG PLB HPURE).

Local Notation shwK1_now := (H_germ_seg2.shwK1_now FI P st m0 A cur RF0 ARNG PLB).
Local Notation blockC1 := (H_germ_seg2.blockC1 FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs CLO LO AL16 QHI RF0 PAL PLO PHI SHWP CURR METHR RMR SCR ISR ARNG PLB HPURE).
Local Notation shwK2_now := (H_germ_seg2.shwK2_now FI P st m0 A cur RF0 ARNG PLB).
Local Notation blockD1 := (H_germ_seg2.blockD1 FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs CLO LO AL16 QHI RF0 PAL PLO PHI SHWP CURR METHR RMR SCR ISR ARNG PLB HPURE).
Local Notation blockE := (H_germ_seg2.blockE FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs CLO LO AL16 RF0 PAL PLO PHI SHWP METHR ISR ARNG PLB HPURE).
Local Notation blockCnf := (H_germ_seg2.blockCnf FI P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 RF0 ARNG PLB).

Local Notation pinvG_frame := (H_germ_seg3.pinvG_frame P meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree ARNG).
Local Notation pinv_dj_F := (H_germ_seg3.pinv_dj_F FI P st m0 A cur RF0 ARNG PLB).
Local Notation pinv_dj_SF := (H_germ_seg3.pinv_dj_SF FI P st m0 A cur RF0 ARNG PLB).
Local Notation pinv_dj_stk := (H_germ_seg3.pinv_dj_stk P lo CLO PHI).
Local Notation shwE_now := (H_germ_seg3.shwE_now FI P st m0 A cur RF0 ARNG PLB).
Local Notation blockDf := (H_germ_seg3.blockDf FI IC P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs CLO LO AL16 Q63 RF0 PAL PLO PHI SHWP SHWERR TPV ARNG PLB HPURE).

Local Notation le1_smallG := (H_germ_seg4.le1_smallG A cur ARNG).
Local Notation to_lower_nzG := (H_germ_seg4.to_lower_nzG A cur ARNG).
Local Notation te_loopA := (H_germ_seg4.te_loopA FI IC P q st gp tp F_ fc A cur hvs ARNG HPURE).
Local Notation sub_fp_vw := (H_germ_seg4.sub_fp_vw FI P lo q A cur hvs ARNG).
Local Notation vw_ok_1 := (H_germ_seg4.vw_ok_1 A cur hvs ARNG).
Local Notation hview_upd := (H_germ_seg4.hview_upd FI P A cur first hvs ARNG HPURE).

Local Notation blockCf := (H_germ_seg5.blockCf FI IC STACK_MALLOC_2 P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree hvs CLO LO AL16 QHI RF0 FCO PAL PLO PHI SHWP SHWCH ARNG PLB HPURE HAPART FEV).

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

Definition XG (eb0 el0 errw hackw posw entpw clenw espw0 : word) : Z -> mem -> Prop := fun r m' =>
  exists errw' hackw' posw' entpw' clenw',
    pinvG m' (wz (A + cur)) (wz 0) errw' hackw' posw' entpw' clenw' (wz cur) /\ hview m'
    /\ ( (r = 0 /\ posw' = wz 4 /\ entpw' = entpw /\ errw' = errw /\ hackw' = hackw /\ clenw' = clenw)
       \/ (r = 6 /\ posw' = posw /\ (entpw' = wz 2 \/ entpw' = wz 3 \/ entpw' = wz 4) /\ errw' = errw /\ hackw' = hackw)
       \/ (r = 3 /\ posw' = posw /\ entpw' = entpw /\ errw' = wz 411 /\ (hackw' = hackw \/ hackw' = wz 1) /\ clenw' = clenw) ).

#[using="m0 CLO RF0 PHI ARNG PLB HPURE"] Lemma XG_rframe : forall eb0 el0 errw hackw posw entpw clenw espw0 r, rframeG (XG eb0 el0 errw hackw posw entpw clenw espw0 r).
Proof.
  intros eb0 el0 errw hackw posw entpw clenw espw0 r m m' (errw' & hackw' & posw' & entpw' & clenw' & PINV & HV & CASES) MU WM.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  exists errw', hackw', posw', entpw', clenw'. split; [| split; [| exact CASES]].
  - eapply pinvG_frame; [exact PINV| exact MU| exact WM|]. intros X n HR. unfold WEG. cbn [disjoint_from].
    split; [clear - HR CLO PHI ACR; lia|]. split; [clear - HR PFAP GF1 FSB1; lia|].
    split; [clear - HR ESF ESHB EKF EKB GF1 GF2 PFS1 PFS2 FSB1 FSB2 FSB5 ACR; lia|]. split; [clear - HR PFS1 PFS2 GF4 GF5 FSB1 PFAP; lia| exact I].
  - eapply hview_frame; [exact HV| exact MU| exact WM|]. apply hsafe_of. unfold H_germ_seg1.WEG, hsafe_iv.
    apply Forall_cons; [left; cbn [fst]; exact CLO|]. apply Forall_cons; [right; left; cbn [fst snd]; clear - GF1 GF2; lia|].
    apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - GF4 GF5; lia| apply Forall_nil].
Qed.

#[using="A cur ARNG"] Lemma postG_weaken : forall VWc X ms, vw_ok VWc -> postG VWc X ms -> postG (hvW hvs) X ms.
Proof.
  intros VWc X ms OK (r & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & MU & REST).
  exists r, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st'. split; [exact E|]. split; [| exact REST].
  eapply munch_weaken; [exact (sub_fp_vw VWc OK)| exact MU].
Qed.

#[using="IC SET_SHADOW_F5 kq kP CLO LO AL16 QHI Q63 RF0 PAL PLO PHI SHWP SHWERR TPV CURR METHR RMR SCR ISR ARNG PLB HPURE"] Lemma tailG : forall VWc q' m v0 v8 v16 v24 eb0 el0 errw hackw posw entpw clenw espw0
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31,
  vw_ok VWc -> minvG VWc q' m 248 248 248 v0 v8 v16 v24 -> pinvG m (wz (A + cur)) (wz 0) errw hackw posw entpw clenw (wz cur) -> hview m ->
  evt asegs (postG (hvW hvs) (XG eb0 el0 errw hackw posw entpw clenw espw0))
    (GSTP 0x896a4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 (P + 288)) x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros VWOK INV PINV HV.
  eapply (blockD1 VWc); [exact VWOK| exact INV| exact PINV| exact HV|].
  intros m1 r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV1 PINV1 HV1 RES.
  destruct RES as [-> | (h & Hh & <- & _)].
  - eapply (blockE VWc); [exact VWOK| exact INV1| exact PINV1| exact HV1|].
    intros m2 r errw' hackw' entpw' z10 z11 z12 z13 z14 z15 z16 z17 INV2 PINV2 HV2 CASES.
    eapply evt_mono; [| intros ms' PO; exact (postG_weaken VWc _ ms' VWOK PO)].
    eapply (exitG r VWc (XG eb0 el0 errw hackw posw entpw clenw espw0)); [exact INV2| | apply XG_rframe].
    exists errw', hackw', posw, entpw', clenw. split; [exact PINV2|]. split; [exact HV2|].
    destruct CASES as [(-> & -> & -> & HK)|(-> & -> & -> & ->)]; [right; right; repeat split; auto| right; left; repeat split; auto].
  - eapply (blockDf VWc h); [exact Hh| exact VWOK| exact INV1| exact PINV1| exact HV1|].
    intros m2 clenw' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z21 z22 z23 z24 z25 z28 z29 z30 z31 INV2 PINV2 HV2.
    eapply evt_mono; [| intros ms' PO; exact (postG_weaken VWc _ ms' VWOK PO)].
    eapply (exitG 6 VWc (XG eb0 el0 errw hackw posw entpw clenw espw0)); [exact INV2| | apply XG_rframe].
    exists errw, hackw, posw, (wz 2), clenw'. split; [exact PINV2|]. split; [exact HV2|]. right; left. repeat split; auto.
Qed.

#[using="CLO ARNG PLB"] Lemma pinvG_prologue : forall m eb el errw hackw posw entpw clenw espw,
  pinvG m0 eb el errw hackw posw entpw clenw espw -> munch ((lo, q) :: FSIV [])%Z m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
  pinvG m eb el errw hackw posw entpw clenw espw.
Proof.
  intros m eb el errw hackw posw entpw clenw espw (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC) MU WM FK.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5).
  assert (SHB : 2147450880 <= sh (FSB FI)) by (unfold sh, SHADOW_OFF; clear - B1; Z.div_mod_to_equations; lia).
  assert (TRP : forall X cs, rw_cells asegs m0 X cs -> P <= X -> X + Z.of_nat (cells_size cs) <= P + 504 -> rw_cells asegs m X cs).
  { intros X cs H H1 H2. eapply (rw_cells_fkeep FI [] st m0 m X cs H FK WM); [left; eapply lb_sub; [exact PLBv| lia| lia]| exact I]. }
  assert (TRL : forall X cs, rw_cells asegs m0 X cs -> 0 <= X -> X + Z.of_nat (cells_size cs) <= 0x609000 -> rw_cells asegs m X cs).
  { intros X cs H H1 H2. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. cbn [disjoint_from]. clear - H1 H2 CLO ACR B1 SHB. lia. }
  unfold pinvG. unfold llist_cells, mbuf_cells in *.
  split; [apply TRP; [exact PM| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRP; [exact PRS| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [exists pad; apply TRP; [exact PV| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRP; [exact PL| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRP; [exact PE| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRP; [exact PMB| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRP; [exact PC| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRP; [exact PS| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [exists ev; apply TRL; [exact PERR| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRL; [exact PGOT| lia| cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TRL; [exact PCAN| lia| cbn [cells_size csize Nat.add]; lia]|].
  apply TRL; [exact PIWC| lia| cbn [cells_size csize Nat.add]; lia].
Qed.

#[using="IC STACK_MALLOC_3 STACK_MALLOC_2 SET_SHADOW_F5 kq kP CLO LO AL16 QHI Q63 RF0 FCO FE0 PAL PLO PHI SHWP SHWCH SHWERR TPV CURR METHR RMR SCR ISR ARNG PLB HPURE HAPART HV0 FEV"] Theorem germ_seg : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 eb el errw hackw posw entpw clenw espw,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 -> pinvG m0 eb el errw hackw posw entpw clenw espw ->
  evt asegs (postG (hvW hvs) (XG eb el errw hackw posw entpw clenw espw))
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 germ_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros until espw. intros ST MI AE PINV0.
  eapply prologueG; [exact ST| exact MI| exact AE|].
  intros q' m v0 v8 v16 v24 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV MUP FKP.
  assert (WMm : wmono asegs m0 m) by (destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _); exact W).
  pose proof (pinvG_prologue m _ _ _ _ _ _ _ _ PINV0 MUP WMm FKP) as PINV.
  eapply blockA; [exact INV| exact PINV| |].
  -
    intros m1 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 INV1 PINV1.
    eapply evt_mono; [| intros ms' PO; exact (postG_weaken [] _ ms' vw_ok_nil PO)].
    eapply (exitG 0 [] (XG eb el errw hackw posw entpw clenw espw)); [exact INV1| | apply XG_rframe].
    exists errw, hackw, (wz 4), entpw, clenw. split; [exact PINV1|]. split; [| left; repeat split; auto].
    destruct INV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU1 & WM1 & _). exact (hview_now0 m1 MU1 WM1).
  - intros m1 y10 y11 y12 y13 y14 y15 y16 y17 INV1 PINV1.
    assert (HV1 : hview m1) by (destruct INV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU1 & WM1 & _); exact (hview_now0 m1 MU1 WM1)).
    eapply blockC1; [exact INV1| exact PINV1| exact HV1|].
    intros m2 r z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 INV2 PINV2 HV2 RES.
    destruct RES as [-> | (h & Hh & <- & _)].
    + eapply blockCnf; [exact INV2|]. intros m3 w10 INV3 MU3 WM3.
      eapply (tailG [] q' m3); [exact vw_ok_nil| exact INV3| | ].
      * eapply pinvG_frame; [exact PINV2| exact MU3| exact WM3| exact pinv_dj_SF].
      * destruct INV3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MUx & WMx & _). exact (hview_now0 m3 MUx WMx).
    + eapply (blockCf h); [exact Hh| exact INV2| exact PINV2| exact HV2| |].
      * intros m3 w0 w8 w16 w24 y1 y5 y6 y7 u10 u11 u12 u13 u14 u15 u16 u17 u21 u22 u23 u24 u25 u28 u29 u30 u31 INV3 PINV3 HV3.
        eapply evt_mono; [| intros ms' PO; exact (postG_weaken (VW1 h) _ ms' (vw_ok_1 h Hh) PO)].
        eapply (exitG 6 (VW1 h) (XG eb el errw hackw posw entpw clenw espw)); [exact INV3| | apply XG_rframe].
        exists errw, hackw, posw, (wz 3), clenw. split; [exact PINV3|]. split; [exact HV3|]. right; left. repeat split; auto.
      * intros m3 w0 w8 w16 w24 y1 y5 y6 y7 u10 u11 u12 u13 u14 u15 u16 u17 u24 u25 u28 u29 u30 u31 INV3 PINV3 HV3.
        eapply (tailG (VW1 h) q' m3); [exact (vw_ok_1 h Hh)| exact INV3| exact PINV3| exact HV3].
Qed.

End W.
