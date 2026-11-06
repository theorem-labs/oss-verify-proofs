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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import H_germ_seg1 H_germ_seg3 H_germ_seg4.

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

#[using="IC STACK_MALLOC_2 kq kP CLO LO AL16 QHI RF0 FCO PAL PLO PHI SHWP SHWCH ARNG PLB HPURE HAPART FEV"] Lemma blockCf : blockCf_stmt.
Proof.
  unfold blockCf_stmt. intros until x31. intros Hh INV PINV HV Q Kc Kn.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
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
  hideW MU WM.
  pose proof (munch_refl [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ RN ACR. lia. } clear KZ.
  walk_lia_to 0x89510.
  step.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 11 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  zstep. zstep. zstep.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  assert (FSWC : Forall (fsw_iv FI) [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z).
  { apply Forall_cons; [left; apply app_iv_stack; exact CLO|]. apply Forall_cons; [right; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - PFS1 PFS2 FSB1 FSB2 FSB5; lia|].
    apply Forall_cons; [left; unfold app_iv, SH_HI; cbn [fst snd]; clear - RV; lia| apply Forall_nil]. }
  assert (SHVa : shw ma (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m ma); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
  assert (CONTa : forall y11 y12, evt asegs Q (GSTP 0x89558 q' x1 x5 x6 x7 (Z_to_bv 64 (hvA h + hvLen h)) y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 P)
                    (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 (P + 288)) (Z_to_bv 64 (hvA h)) x25 x28 x29 x30 x31 ma)).
  { intros y11 y12.
    step. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mb end.
    assert (SHVb : shw mb (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m mb); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
    chkbN 11 (hvA h) SHVb kv SHRv Hkv.
    step. step.
    pose proof (u8arr_read asegs _ _ vbs (hvLen h) zbG (Z_to_bv 64 (hvA h + hvLen h)) (u8arr_of_rw_cells asegs _ _ _ _ VB) VN ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. cbv beta. clear RD. step; fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mX end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mX end.
    assert (CONTb : forall z11 z12, evt asegs Q (GSTP 0x89578 q' x1 x5 x6 x7 (Z_to_bv 64 0) z11 z12 x13 x14 x15 x16 x17 (Z_to_bv 64 P)
                      (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 (P + 288)) (Z_to_bv 64 (hvA h)) x25 x28 x29 x30 x31 mX)).
    { intros z11 z12.
      pose proof VN as VN2. apply List.nth_error_split in VN2 as (l1 & l2 & EV0 & LL1).
      assert (NS : exists str rest, vbs = str ++ zbG :: rest /\ ~ In zbG str /\ (length str <= length l1)%nat).
      { rewrite EV0. clear. induction l1 as [|a l IH]; [exists [], l2; split; [reflexivity|]; split; [intros []| cbn; lia]|].
        destruct (bv_eq_dec 8 a zbG) as [->|NE]; [exists [], (l ++ zbG :: l2); split; [reflexivity|]; split; [intros []| cbn; lia]|].
        destruct IH as (s & r & E & NIs & LE). exists (a :: s), r. split; [cbn; rewrite E; reflexivity|].
        split; [intros [E1|E1]; [apply NE; exact E1| exact (NIs E1)]| cbn; lia]. }
      destruct NS as (str & rest & EV & NI & LSTR).
      assert (LVB : Z.of_nat (length vbs) = hvCap h + 1) by (destruct VB as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); rewrite W0; clear - LC; lia).
      assert (SHVX : shw mX (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m mX); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
      pose proof (u8arr_of_rw_cells asegs _ _ _ _ VB) as WBX.
      assert (CONTx : forall m' vbs' c1 c5 c6 c7 c10 c11 c12 c13 c14 c15 c16 c17 c23 c25 c28 c29 c30 c31,
         u8arr asegs m' (hvA h) vbs' -> linvG vbs vbs' (length str) -> mem_inv asegs m' ->
         munch [(hvA h, hvA h + (hvCap h + 1))]%Z mX m' -> wmono asegs mX m' ->
         evt asegs Q (GSTP 0x895e8 q' c1 c5 c6 c7 c10 c11 c12 c13 c14 c15 c16 c17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) c23 (Z_to_bv 64 (hvA h)) c25 c28 c29 c30 c31 m')).
      { intros m' vbs' c1 c5 c6 c7 c10 c11 c12 c13 c14 c15 c16 c17 c23 c25 c28 c29 c30 c31 WB' LI' MI'' MUv WMv.
        clear VB WBX SHVX MI.

        clear Hkv SHRv SHVa SHVb N1 N2 N3 I1 I2 I3 RN RI. try clear VC. try clear NC.
        transport_after_call asegs mX m' MUv WMv. clear MUv WMv.
        assert (SHV' : shw m' (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m m'); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
        step.
        assert (CONTy : forall y10 y11, evt asegs Q (GSTP 0x895f4 q' c1 c5 c6 c7 y10 y11 c12 c13 c14 c15 c16 c17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 ((hvA h + hvLen h) ≫ 3 + 2147450880)) (Z_to_bv 64 (hvA h)) c25 c28 c29 c30 c31 m')).
        2:{ chkbN 23 (hvA h + hvLen h) SHV' kk SHRk Hk.
            destruct Hk as [-> | [G1 G2]].
            - step. step. lit_branch. apply CONTy.
            - step. rewrite (sxb_small kk) by lia.
              step. if_cases G3; zify_cond G3; [| exfalso; lia].
              step. zstep.
              step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
              apply CONTy. }
        { intros u10 u11.
          step.
          pose proof LI' as (LL & LGE & LLT & LZ).
          assert (LVB' : Z.of_nat (length vbs') = hvCap h + 1) by (rewrite LL; exact LVB).
          pose proof (u8arr_store_ok asegs _ _ _ (hvLen h) (Z_to_bv 64 (hvA h + hvLen h + 0)) WB' ltac:(rewrite LVB'; clear - LC; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
          zstep.
          assert (LE10 : le1 (Z_to_bv 64 0) = [zbG]) by (unfold le1; rewrite unsigned_lit by lia; reflexivity).
          rewrite LE10. clear LE10.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
            change (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (hvA h + hvLen h)) x) end.
          replace (hvA h + hvLen h + 0) with (hvA h + hvLen h) in SOK by lia.
          pose proof (u8arr_write asegs _ _ _ (hvLen h) zbG WB' ltac:(rewrite LVB'; clear - LC; lia)) as WB2. clear WB'.
          store_done.
          assert (UPDID : forall (l : list byte) i x, nth_error l i = Some x -> upd l i x = l).
          { clear. induction l as [|y l IH]; intros [|i] x Hx; cbn in *; try discriminate; [injection Hx as ->; reflexivity| rewrite (IH i x Hx); reflexivity]. }
          rewrite (UPDID vbs' _ zbG (LZ _ VN)) in WB2.
          assert (FZ : nth_error vbs (length str) = Some zbG) by (rewrite EV, nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
          pose proof (LZ _ FZ) as SP. apply List.nth_error_split in SP as (hay & rest' & EV' & LHAY).
          assert (NIH : ~ In zbG hay).
          { intros HIn. apply In_nth_error in HIn as (j & Hj). assert (j < length hay)%nat by (apply nth_error_Some; rewrite Hj; discriminate).
            refine (LLT j zbG ltac:(lia) _ eq_refl). rewrite EV', nth_error_app1 by lia. exact Hj. }
          assert (LR' : Z.of_nat (length hay) + 1 + Z.of_nat (length rest') = hvCap h + 1).
          { rewrite <- LVB', EV', length_app. cbn [length]. lia. }
          assert (BYH : bytes_at asegs m1 (hvA h) (hay ++ zbG :: (rest' ++ sl))).
          { replace (hay ++ zbG :: rest' ++ sl) with (vbs' ++ sl) by (rewrite EV', <- app_assoc; reflexivity).
            apply bytes_at_app. split; [exact (proj1 WB2)|]. rewrite LVB'. exact SL. }
          pose proof (rw_cells_of_u8arr asegs _ _ _ WB2) as VB2. clear WB2.
          replace (length vbs') with (Z.to_nat (hvCap h + 1)) in VB2 by (clear - LVB'; lia).
          assert (SHWCH1 : shw m1 A0_CHUNKED 8).
          { eapply (shw_frame_fs FI _ m m1); [eapply (shw_frame_fs FI (W0c []) m0 m); [exact SHWCH| exact MU| exact (W0c_fsw [] vw_ok_nil)| left; unfold A0_CHUNKED; clear - FSB1; lia] | exact MU0| exact FSWC| left; unfold A0_CHUNKED; clear - FSB1; lia]. }
          assert (SHV1 : shw m1 (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m m1); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
          assert (LHC : Z.of_nat (length hay) <= hvCap h) by (clear - LR'; lia).
          destruct (shw_sub _ _ _ (hvA h) (Z.of_nat (length hay) + 1) SHV1 ltac:(lia) ltac:(clear - LHC; lia) ltac:(lia)) as (ACS & RDS & _).
          destruct SHWCH1 as (ACN & RDN & _).
          env_sync AE MU0 WM0.
          zstep. zstep. zstep. step.
          eapply evt_cut.
          { eapply (ic_strstr_chunked IC) with (H := hvA h) (hay := hay) (slack := rest' ++ sl) (canary := canary) (lo := lo) (q := q');
              [ exact BYH | exact NIH
              | rewrite length_app, Nat2Z.inj_add; clear - LR' SE SLL; Z.div_mod_to_equations; lia
              | exact PGOT | exact PCAN
              | exact ACS | exact RDS | unfold icpt_win; clear - LHC RV ACR; lia | clear - LHC CAPB; lia
              | exact ACN | exact RDN
              | exact AE | exact ST | exact CLO | unfold A0_STRSTR_DEPTH; clear - LO Hq; lia | clear - QHI Hq; lia
              | clear - RV; lia | rewrite length_app, Nat2Z.inj_add; clear - LR' SLL RV; lia
              | exact MI'' | reflexivity | reflexivity ]. }
          intros msS PS0. unfold strstr_chunked_post_A in PS0.
          destruct PS0 as (d0 & d1 & d2 & d4 & d5 & d6 & d7 & d8 & d9 & d10 & d11 & d12 & d13 & d14 & m2 & r & -> & MUc & WMc & MI2 & ST2 & AE2 & BYH2 & PGOT2 & PCAN2 & RR).
          clear BYH ACS RDS ACN RDN SHV1 MI'' ST AE PGOT PCAN.
          transport_after_call asegs m1 m2 MUc WMc.
          lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
          clear MUc WMc. unfold A0_got_ssp in PGOT2. unfold A0_ssp_guard in PGOT2, PCAN2.
          assert (SHV2 : shw m2 (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m m2); [exact SHV| exact MU0| exact FSWC| clear - RV; lia]).
          assert (CONTz : forall z11 z12, evt asegs Q (GSTP 0x89618 q' (Z_to_bv 64 562700) d0 d1 d2 (Z_to_bv 64 r) z11 z12 d6 d7 d8 d9 d10 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 (P + 288)) (Z_to_bv 64 (hvA h)) (Z_to_bv 64 (hvA h + hvLen h)) d11 d12 d13 d14 m2)).
          2:{ chkbN 23 (hvA h + hvLen h) SHV2 kk SHRk Hk.
              destruct Hk as [-> | [G1 G2]].
              - step. step. step. lit_branch. apply CONTz.
              - step. rewrite (sxb_small kk) by lia. step.
                step. if_cases G3; zify_cond G3; [| exfalso; lia].
                zstep.
                step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
                apply CONTz. }
          { intros t11 t12.
            clear BYH2 AE2. change (hid2 (r = 0 \/ hvA h <= r <= hvA h + Z.of_nat (length hay))) in RR.
            pose proof (LZ _ VN) as NZ.
            clear LSTR LL1 LHAY EV0 LL LR' LGE LLT LI' LZ FZ NIH NI EV EV' LVB.
            step.
            pose proof (u8arr_of_rw_cells asegs _ _ _ _ VB2) as WB3. clear VB2.
            pose proof (u8arr_store_ok asegs _ _ _ (hvLen h) (Z_to_bv 64 (hvA h + hvLen h)) WB3 ltac:(rewrite LVB'; clear - LC; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
            zstep.
            assert (LE10 : le1 (Z_to_bv 64 0) = [zbG]) by (unfold le1; rewrite unsigned_lit by lia; reflexivity).
            rewrite LE10. clear LE10.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
              change (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (hvA h + hvLen h)) x) end.
            pose proof (u8arr_write asegs _ _ _ (hvLen h) zbG WB3 ltac:(rewrite LVB'; clear - LC; lia)) as WB4. clear WB3.
            store_done.
            rewrite (UPDID vbs' _ zbG NZ) in WB4.
            pose proof (rw_cells_of_u8arr asegs _ _ _ WB4) as VB4. clear WB4.
            replace (length vbs') with (Z.to_nat (hvCap h + 1)) in VB4 by (clear - LVB'; lia).

            assert (HS3 : hsafeW [(lo, q); (SF, SF + 64); (P + 440, P + 480)]%Z).
            { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [left; cbn [fst]; exact CLO|].
              apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
              apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia| apply Forall_nil]. }
            assert (DJ4 : forall X n n', hreg X n -> 0 <= n' <= ru8G (X + n) - X -> (X + n' <= hvA h \/ hvA h + (hvCap h + 1) <= X) ->
                     disjoint_from [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z X n').
            { intros X n n' HR Hn' D4. pose proof (proj2 HS3 X n HR) as D3. cbn [disjoint_from] in D3 |- *. destruct D3 as (D1 & D2 & D3 & _).
              split; [clear - D1 Hn'; lia|]. split; [clear - D2 Hn'; lia|]. split; [clear - D3 Hn'; lia|]. split; [exact D4| exact I]. }
            assert (HV3 : hview m3).
            { eapply (hview_upd h _ m m3 Hh HV MU0 WM0 FSWC).
              - intros h' Hh'. destruct (HPURE h' Hh') as (_ & _ & RN' & RI' & _). destruct (HAPART h h' Hh Hh') as (A1 & A2 & _).
                pose proof (ru8G_spec (hvN h' + 24)) as (U1 & _). pose proof (ru8G_spec (hvIt h' + 88)) as (U2 & _).
                split; [apply (DJ4 _ 24 24 RN'); [clear - U1; lia| clear - A1 RU1; lia] | apply (DJ4 _ 88 88 RI'); [clear - U2; lia| clear - A2 RU1; lia]].
              - intros h' Hh'. destruct (HPURE h' Hh') as (LC' & _ & _ & _ & RV'). destruct (HAPART h h' Hh Hh') as (_ & _ & [(E1 & E2 & E3)|A3]); [left; repeat split; symmetry; assumption| right].
                pose proof (ru8G_spec (hvA h' + (hvCap h' + 1))) as (U3 & _).
                apply (DJ4 _ (hvCap h' + 1) (ru8G (hvA h' + (hvCap h' + 1)) - hvA h') RV'); [clear - LC' U3; lia| clear - A3 RU1 U3; lia].
              - assert (RVh : hreg (hvA h) (hvCap h + 1)) by exact RV.
                pose proof (proj2 HS3 _ _ RVh) as D3. cbn [disjoint_from] in D3 |- *. destruct D3 as (D1 & D2 & D3 & _).
                split; [clear - D1 LC; lia|]. split; [clear - D2 LC; lia|]. split; [clear - D3 LC; lia|]. split; [right; lia| exact I].
              - exists vbs'. split; [exact VB4| exact NZ]. }
            assert (SUB01 : sub_fp (W0c []) (W0c (VW1 h))).
            { intros xo Ho. cbn [outside app VW1] in *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat (split; [assumption|]). exact I. }
            assert (SUBC : sub_fp [(lo, q); (SF, SF + 64); (P + 440, P + 480); (hvA h, hvA h + (hvCap h + 1))]%Z (W0c (VW1 h))).
            { intros xo Ho. cbn [outside app VW1] in *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
              split; [exact H1|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [exact H5|]. split; [exact H7| exact I]. }
            assert (MUw : hid2 (munch (W0c (VW1 h)) m0 m)) by exact (munch_weaken (W0c []) (W0c (VW1 h)) m0 m SUB01 MU).
            clear MU. rename MUw into MU.
            absorbW MU WM MU0 WM0 SUBC.
            env_sync AEs MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
            unfold hid2 in RR.
            step. if_cases K0; zify_cond K0.
            {
              eapply (Kn m3); [mv_tacG | pv_tacG | exact HV3]. }
            destruct RR as [E0|RR]; [exfalso; exact (K0 E0)|]. clear K0.
            zstep. zstep. zstep.
            assert (A0Z : (bv_swrap 32 (bv_wrap 32 (bv_swrap 32 (r - hvA h) mod 18446744073709551616) ≫ 31) mod 18446744073709551616) ≪ 31 = 0).
            { assert (DR : 0 <= r - hvA h < 2^31) by (clear - RR LHC CAPB; lia).
              assert (SW : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
              { intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia. }
              replace (bv_swrap 32 (r - hvA h)) with (r - hvA h) by (symmetry; apply SW; lia).
              rewrite (Z.mod_small (r - hvA h)) by lia.
              replace (bv_wrap 32 (r - hvA h)) with (r - hvA h) by (unfold bv_wrap; change (bv_modulus 32) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
              rewrite (Z.shiftr_div_pow2 _ 31) by lia. rewrite (Z.div_small (r - hvA h)) by lia. reflexivity. }
            rewrite A0Z. clear A0Z.
            step. lit_branch.

            clear RR LHC.
            pose proof (shwP_now m3 FK) as SHWPs.
            pose proof (munch_refl WPg m3) as MU0. pose proof (wmono_refl asegs m3) as WM0.
            hideW MU WM.
            wPA SHWPs MU0 SHWPn 0x8966c.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mP end.
            assert (HSP : hsafeW WPg).
            { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|].
              apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|]. apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia| apply Forall_nil]. }
            pose proof (hview_frame _ m3 mP HV3 MU0 WM0 HSP) as HVP.
            pose proof (sub_fp_WPg (VW1 h)) as SUBW.
            absorbW MU WM MU0 WM0 SUBW. env_sync AEs MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
            pose proof (FEV mP (munch_weaken _ _ m0 mP (sub_fp_vw (VW1 h) (vw_ok_1 h Hh)) MU) WM) as FEP.
            hideW MU WM.
            step.
            eapply evt_cut.
            { eapply (UpnpPrintf_spec_A FI STACK_MALLOC_2) with (lo := lo) (st := stc);
                [ exact PIWC | exact ST2 | exact CLO | unfold A0_RT_STACK; clear - LO Hq; lia | clear - Hq32; Z.div_mod_to_equations; lia | clear - Hq QHI; lia
                | exact MI2 | exact AEs | exact RF | exact (fs_call_ok_push FI st stc tp 1%nat _ FCO LIVE1) | exact FEP ]. }
            intros msU POU. unfold UpnpPrintf_post_A in POU.
            destruct POU as (g5 & g6 & g7 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & mU & stU & -> & MUc & WMc & MIU & FKc & LIVEc & RFU & STU & AEU & PIWCU).
            replace (ret_pc (Z_to_bv 64 562800)) with (Z_to_bv 64 562800) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

            fk_move LE FKc WMc. fk_move LJ1 FKc WMc. fk_move LK2 FKc WMc. fk_move LR2 FKc WMc. fk_move LK1 FKc WMc. fk_move LR1 FKc WMc.
            fk_move FH FKc WMc. fk_move FT FKc WMc. fk_move SHF FKc WMc. fk_move FLG FKc WMc.
            fk_move PM FKc WMc. fk_move PRS FKc WMc. fk_move PV FKc WMc. fk_move PL FKc WMc. fk_move PE FKc WMc. fk_move PMB FKc WMc. fk_move PC FKc WMc. fk_move PS FKc WMc.
            clear ST2 AEs MI2 RF PIWC SHWPs SHWPn FEP.
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
            eapply (Kc mU); [mv_tacG | pv_tacG | exact HVU]. }
        }
      }
      assert (Hb0 : exists b0, nth_error vbs 0 = Some b0) by (rewrite EV; destruct str; cbn; eexists; reflexivity).
      destruct Hb0 as (b0 & Hb0).
      pose proof (u8arr_read asegs _ _ vbs 0 b0 (Z_to_bv 64 (hvA h)) WBX Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
      zstep. cbv beta. clear RD0.
      assert (LI0 : forall i, (i <= length str)%nat -> linvG vbs vbs i).
      { intros i Hi. split; [reflexivity|]. split; [intros j _; reflexivity|]. split; [| intros j Hj; exact Hj].
        intros j b Hj Hb E0. apply NI. rewrite EV, nth_error_app1 in Hb by lia. assert (b = zbG) as <- by (apply bv_eq; rewrite E0; reflexivity). eapply nth_error_In. exact Hb. }
      step. if_cases K0; zify_cond K0.
      -
        eapply (CONTx mX vbs); [exact WBX| exact (LI0 _ (Nat.le_refl _))| exact MI| apply munch_refl| apply wmono_refl].
      - zstep. zstep.
        assert (LS0 : (0 < length str)%nat).
        { destruct str as [|c0 str0]; [| cbn; lia]. exfalso. apply K0. rewrite EV in Hb0. cbn in Hb0. injection Hb0 as <-. reflexivity. }
        pose proof (te_loopA h vbs str rest mX Q q' _ _ Hh EV NI LVB SHVX CONTx (S (length str)) 0%nat vbs b0 mX) as TL.
        cbn [Z.of_nat] in TL. rewrite Z.add_0_r in TL.
        eapply TL; [lia| exact LS0| exact Hb0| apply munch_refl| apply wmono_refl| exact MI| exact WBX| exact (LI0 0%nat ltac:(lia))].
    }
    destruct Hkv as [-> | [G1 G2]].
    - step. lit_branch. apply CONTb.
    - rewrite (sxb_small kv) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONTb.
  }
  chkbN 11 (hvA h + hvLen h) SHVa kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONTa.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONTa.
Qed.

End W.
