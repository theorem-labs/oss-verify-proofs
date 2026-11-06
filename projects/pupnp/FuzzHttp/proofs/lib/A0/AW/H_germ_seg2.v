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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import H_germ_seg1.

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

#[using="P m0 A cur RF0 ARNG PLB"] Lemma shwK1_now : forall m w1 w2, rw_cells asegs m SF (gshadow w1 w2 0) -> shw m (F + 192) 88.
Proof.
  intros m w1 w2 SHF.
  destruct geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (FAL : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (rw_cells asegs m (sh F) (shadow_cells [241; 241; 241; 241; w1; 242; 242; 242; w2; w2; w2; w2; w2; w2; w2; w2; w2; w2; w2;
            242; 242; 242; 242; 242; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 243; 243; 243; 243; 243;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) in SHF.
  assert (S32 : sh (F + 192) = sh F + 24) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (S287 : sh (F + 192 + 88 - 1) = sh F + 34) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (SM : sh F mod 8 = 0) by (unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia).
  split; [| split].
  - apply (accessible_of_chunk m F _ (F + 192) 88 SHF FAL); [lia| cbn [length]; lia|].
    intros i Hi H1 H2. cbn [length] in Hi.
    do 35 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). exfalso. lia.
  - apply (sh_readable_of_chunk m F _ (F + 192) 88 SHF).
    + rewrite S32. clear - SM. Z.div_mod_to_equations. lia.
    + rewrite S287. cbn [length]. clear - SM. Z.div_mod_to_equations. lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. lia.
Qed.

#[using="kq kP CLO LO AL16 QHI RF0 PAL PLO PHI SHWP CURR METHR RMR SCR ISR ARNG PLB HPURE"] Lemma blockC1 : forall q' m v0 v8 v16 v24 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31,
  minvG [] q' m 248 248 248 v0 v8 v16 v24 -> pinvG m eb el errw hackw posw entpw clenw espw -> hview m ->
  forall (Q : machine_state -> Prop),
  (forall m' (r : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvG [] q' m' 248 248 0 v0 v8 v16 v24 -> pinvG m' eb el errw hackw posw entpw clenw espw -> hview m' ->
     (r = 0 \/ exists h, In h hvs /\ hvN h = r /\ hvId h = 22) ->
     evt asegs Q (GSTP 0x894c4 q' y1 y5 y6 y7 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 P) x21 x22 (Z_to_bv 64 (P + 288)) x24 x25 y28 y29 y30 y31 m')) ->
  evt asegs Q (GSTP 0x8947c q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 x22 x23 x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV HV Q K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  pose proof (shwP_now m FK) as SHWPs.
  pose proof (munch_refl [(SF, SF + 64); (F + 192, F + 212)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  unfold mbuf_cells in PMB. unfold llist_cells in PL.
  hideW MU WM.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  step. do 11 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  step. step; fix_lit_store. step. step. step. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  assert (HSW : hsafeW [(SF, SF + 64); (F + 192, F + 212)]%Z).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - GF1 GF2; lia| apply Forall_nil]. }
  pose proof (hview_frame _ m mc HV MU0 WM0 HSW) as HVc. pose proof HVc as (LSc & HIc).
  assert (SUB0 : sub_fp [(SF, SF + 64); (F + 192, F + 212)]%Z (W0c [])) by (apply sub_fp_cons2; [apply sub_fp_SF| apply sub_fp_F; clear; lia]).
  absorbW MU WM MU0 WM0 SUB0.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  pose proof (shwP_now mc FK) as SHWPc. pose proof (shwK1_now mc _ _ SHF) as SHWKc.
  replace (P + 312) with (P + 288 + 24) in LSc by (clear; lia).
  assert (OBL : objA mc (P + 288) 96).
  { split; [clear - PLO; lia|]. split; [clear - PHI; lia|]. split; [clear - PAL; Z.div_mod_to_equations; lia|]. eapply shw_sub; [exact SHWPc| lia| lia| lia]. }
  assert (OBK : objA mc (F + 192) 24).
  { split; [clear - GF1 FSB1; lia|]. split; [clear - GF2 FSB2; lia|]. split; [clear - EKF; Z.div_mod_to_equations; lia|]. eapply shw_sub; [exact SHWKc| lia| lia| lia]. }
  assert (OBN : forall N it id, In (N, it, id) (map hv3 hvs) -> objA mc N 24 /\ objA mc it 24).
  { intros N it id Hin. apply in_map_iff in Hin as (h & E & Hh). unfold hv3 in E. injection E as <- <- <-.
    destruct (HIc h Hh) as (ON & (I1 & I2 & I3 & I4) & _). split; [exact ON|].
    split; [exact I1|]. split; [lia|]. split; [exact I3|]. eapply shw_sub; [exact I4| lia| lia| lia]. }
  eapply evt_cut.
  { eapply (ListFind_spec_A (P + 288) (F + 192) 22 last size flh fk ffree lo (map hv3 hvs) k1) with (first := first);
      [ exact PL | exact LSc | exact LK1 | clear; lia | exact OBL | exact OBK | exact OBN | exact AE | exact ST | exact CLO
      | clear - LO Hq; lia | clear - QHI Hq; lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold ListFind_post_A in PO.
  destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m' & r & -> & MUc & WMc & MI' & ST' & AE' & RES).
  transport_after_call asegs mc m' MUc WMc.
  assert (HV' : hview m').
  { eapply (hview_frame [(lo, q')]%Z mc m' HVc MUc WMc). apply hsafe_of. apply Forall_cons; [left; cbn [fst]; exact CLO| apply Forall_nil]. }
  rename MUc into MU0. rename WMc into WM0. clear AE. rename AE' into AE.
  fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  eapply K; [mv_tacG| pv_tacG| exact HV'|].
  destruct RES as [R0|(it & Hin)]; [left; exact R0| right].
  apply in_map_iff in Hin as (h & E & Hh). unfold hv3 in E. injection E as E1 E2 E3. exists h. split; [exact Hh|]. split; [exact E1| exact E3].
Qed.

#[using="P m0 A cur RF0 ARNG PLB"] Lemma shwK2_now : forall m w1 w3, rw_cells asegs m SF (gshadow w1 0 w3) -> shw m (F + 64) 88.
Proof.
  intros m w1 w3 SHF.
  destruct geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (FAL : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (rw_cells asegs m (sh F) (shadow_cells [241; 241; 241; 241; w1; 242; 242; 242; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
            242; 242; 242; 242; 242; w3; w3; w3; w3; w3; w3; w3; w3; w3; w3; w3; 243; 243; 243; 243; 243;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) in SHF.
  assert (S32 : sh (F + 64) = sh F + 8) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (S287 : sh (F + 64 + 88 - 1) = sh F + 18) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (SM : sh F mod 8 = 0) by (unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia).
  split; [| split].
  - apply (accessible_of_chunk m F _ (F + 64) 88 SHF FAL); [lia| cbn [length]; lia|].
    intros i Hi H1 H2. cbn [length] in Hi.
    do 19 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). exfalso. lia.
  - apply (sh_readable_of_chunk m F _ (F + 64) 88 SHF).
    + rewrite S32. clear - SM. Z.div_mod_to_equations. lia.
    + rewrite S287. cbn [length]. clear - SM. Z.div_mod_to_equations. lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. lia.
Qed.

#[using="kq kP CLO LO AL16 QHI RF0 PAL PLO PHI SHWP CURR METHR RMR SCR ISR ARNG PLB HPURE"] Lemma blockD1 : forall VWc q' m v0 v8 v16 v24 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x28 x29 x30 x31,
  vw_ok VWc -> minvG VWc q' m 248 248 248 v0 v8 v16 v24 -> pinvG m eb el errw hackw posw entpw clenw espw -> hview m ->
  forall (Q : machine_state -> Prop),
  (forall m' (r : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvG VWc q' m' 248 0 248 v0 v8 v16 v24 -> pinvG m' eb el errw hackw posw entpw clenw espw -> hview m' ->
     (r = 0 \/ exists h, In h hvs /\ hvN h = r /\ hvId h = 3) ->
     evt asegs Q (GSTP 0x896e8 q' y1 y5 y6 y7 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 P) x21 x22 (Z_to_bv 64 (P + 288)) x24 x25 y28 y29 y30 y31 m')) ->
  evt asegs Q (GSTP 0x896a4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 x22 (Z_to_bv 64 (P + 288)) x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros VWOK INV PINV HV Q K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  pose proof (shwP_now m FK) as SHWPs.
  pose proof (munch_refl [(SF, SF + 64); (F + 64, F + 84)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  unfold mbuf_cells in PMB. unfold llist_cells in PL.
  hideW MU WM.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  step. do 11 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  step. step; fix_lit_store. step. step. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  assert (HSW : hsafeW [(SF, SF + 64); (F + 64, F + 84)]%Z).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - GF1 GF2; lia| apply Forall_nil]. }
  pose proof (hview_frame _ m mc HV MU0 WM0 HSW) as HVc. pose proof HVc as (LSc & HIc).
  assert (SUB0 : sub_fp [(SF, SF + 64); (F + 64, F + 84)]%Z (W0c VWc)) by (apply sub_fp_cons2; [apply sub_fp_SF| apply sub_fp_F; clear; lia]).
  absorbW MU WM MU0 WM0 SUB0.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  pose proof (shwP_now mc FK) as SHWPc. pose proof (shwK2_now mc _ _ SHF) as SHWKc.
  replace (P + 312) with (P + 288 + 24) in LSc by (clear; lia).
  assert (OBL : objA mc (P + 288) 96).
  { split; [clear - PLO; lia|]. split; [clear - PHI; lia|]. split; [clear - PAL; Z.div_mod_to_equations; lia|]. eapply shw_sub; [exact SHWPc| lia| lia| lia]. }
  assert (OBK : objA mc (F + 64) 24).
  { split; [clear - GF1 FSB1; lia|]. split; [clear - GF2 FSB2; lia|]. split; [clear - EKF; Z.div_mod_to_equations; lia|]. eapply shw_sub; [exact SHWKc| lia| lia| lia]. }
  assert (OBN : forall N it id, In (N, it, id) (map hv3 hvs) -> objA mc N 24 /\ objA mc it 24).
  { intros N it id Hin. apply in_map_iff in Hin as (h & E & Hh). unfold hv3 in E. injection E as <- <- <-.
    destruct (HIc h Hh) as (ON & (I1 & I2 & I3 & I4) & _). split; [exact ON|].
    split; [exact I1|]. split; [lia|]. split; [exact I3|]. eapply shw_sub; [exact I4| lia| lia| lia]. }
  eapply evt_cut.
  { eapply (ListFind_spec_A (P + 288) (F + 64) 3 last size flh fk ffree lo (map hv3 hvs) k2) with (first := first);
      [ exact PL | exact LSc | exact LK2 | clear; lia | exact OBL | exact OBK | exact OBN | exact AE | exact ST | exact CLO
      | clear - LO Hq; lia | clear - QHI Hq; lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold ListFind_post_A in PO.
  destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m' & r & -> & MUc & WMc & MI' & ST' & AE' & RES).
  transport_after_call asegs mc m' MUc WMc.
  assert (HV' : hview m').
  { eapply (hview_frame [(lo, q')]%Z mc m' HVc MUc WMc). apply hsafe_of. apply Forall_cons; [left; cbn [fst]; exact CLO| apply Forall_nil]. }
  rename MUc into MU0. rename WMc into WM0. clear AE. rename AE' into AE.
  fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  eapply K; [mv_tacG| pv_tacG| exact HV'|].
  destruct RES as [R0|(it & Hin)]; [left; exact R0| right].
  apply in_map_iff in Hin as (h & E & Hh). unfold hv3 in E. injection E as E1 E2 E3. exists h. split; [exact Hh|]. split; [exact E1| exact E3].
Qed.

#[using="kq kP CLO LO AL16 RF0 PAL PLO PHI SHWP METHR ISR ARNG PLB HPURE"] Lemma blockE : forall VWc q' m v0 v8 v16 v24 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31,
  vw_ok VWc -> minvG VWc q' m 248 0 248 v0 v8 v16 v24 -> pinvG m eb el errw hackw posw entpw clenw espw -> hview m ->
  forall (Q : machine_state -> Prop),
  (forall m' (r : Z) errw' hackw' entpw' y10 y11 y12 y13 y14 y15 y16 y17,
     minvG VWc q' m' 248 248 248 v0 v8 v16 v24 -> pinvG m' eb el errw' hackw' posw entpw' clenw espw -> hview m' ->
     ((r = 3 /\ errw' = wz 411 /\ entpw' = entpw /\ (hackw' = hackw \/ hackw' = wz 1)) \/ (r = 6 /\ errw' = errw /\ hackw' = hackw /\ entpw' = wz 4)) ->
     evt asegs Q (GSTP 0x89370 q' x1 x5 x6 x7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 r) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x23 x24 x25 x28 x29 x30 x31 m')) ->
  evt asegs Q (GSTP 0x896e8 q' x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x23 x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros VWOK INV PINV HV Q K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  unfold mbuf_cells in PMB. unfold llist_cells in PL.
  hideW MU WM.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. lit_branch. step.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 11 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  assert (HVc : hview mc).
  { eapply (hview_frame _ m mc HV MU0 WM0). apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia| apply Forall_nil]. }
  assert (HSP : hsafeW WPg).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|]. apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia| apply Forall_nil]. }
  absorbW MU WM MU0 WM0 (sub_fp_SF VWc).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  pose proof (shwP_now mc FK) as SHWPs.
  pose proof (munch_refl WPg mc) as MU0. pose proof (wmono_refl asegs mc) as WM0.
  hideW MU WM.
  wPA SHWPs MU0 SHWPn 0x89370.
  assert (SUBW : sub_fp WPg (W0c VWc)) by (intros xo Ho; cbn [outside app] in *; destruct Ho as (_ & _ & _ & H4 & H5 & H6 & _); split; [exact H4|]; split; [exact H5|]; split; [exact H6| exact I]).
  if_cases KI; zify_cond KI.
  -
    wPA SHWPs MU0 SHWPn 0x89370.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (hview_frame _ mc mm HVc MU0 WM0 HSP) as HVK end.
    absorbW MU WM MU0 WM0 SUBW. env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    eapply K; [mv_tacG| pv_tacG| exact HVK| right; repeat split; reflexivity].
  - wPA SHWPs MU0 SHWPn 0x89370.
    if_cases KM; zify_cond KM.
    + wPA SHWPs MU0 SHWPn 0x89370.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (hview_frame _ mc mm HVc MU0 WM0 HSP) as HVK end.
    absorbW MU WM MU0 WM0 SUBW. env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
      eapply K; [mv_tacG| pv_tacG| exact HVK| left; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| left; reflexivity]].
    + wPA SHWPs MU0 SHWPn 0x89370.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (hview_frame _ mc mm HVc MU0 WM0 HSP) as HVK end.
    absorbW MU WM MU0 WM0 SUBW. env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
      eapply K; [mv_tacG| pv_tacG| exact HVK| left; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| right; reflexivity]].
Qed.

#[using="kq A cur CLO LO AL16 RF0 ARNG PLB"] Lemma blockCnf : forall q' m v0 v8 v16 v24
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31,
  minvG [] q' m 248 248 0 v0 v8 v16 v24 ->
  forall (Q : machine_state -> Prop),
  (forall m' y10, minvG [] q' m' 248 248 248 v0 v8 v16 v24 -> munch [(SF, SF + 64)]%Z m m' -> wmono asegs m m' ->
     evt asegs Q (GSTP 0x896a4 q' x1 x5 x6 x7 y10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 x22 x23 x24 x25 x28 x29 x30 x31 m')) ->
  evt asegs Q (GSTP 0x894c4 q' x1 x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 x22 x23 x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV Q K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  hideW MU WM.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. lit_branch. step.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 11 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  pose proof MU0 as MUk. pose proof WM0 as WMk.
  absorbW MU WM MU0 WM0 (sub_fp_SF []).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  eapply K; [mv_tacG| exact MUk| exact WMk].
Qed.

End W.
