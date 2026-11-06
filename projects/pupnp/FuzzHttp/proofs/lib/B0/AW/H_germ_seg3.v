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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import H_germ_seg1.

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

#[using="Type"] Lemma lsegA_node : forall ns m first pv TAIL N it id, lsegA m ns first pv TAIL -> In (N, it, id) ns ->
  exists pv' nx, rw_cells asegs m N (node_cells pv' nx it).
Proof.
  induction ns as [|[[N0 it0] id0] ns IH]; intros m fst0 pv TAIL N it id LS Hin; [destruct Hin|].
  cbn [lsegA] in LS. destruct LS as (_ & _ & _ & _ & _ & nx & n1 & n2 & pad & NC & _ & LS').
  destruct Hin as [E|Hin]; [injection E as <- <- <-; exists pv, nx; exact NC| exact (IH m nx N0 TAIL N it id LS' Hin)].
Qed.

#[using="lo ARNG"] Lemma pinvG_frame : forall W m m' eb el errw hackw posw entpw clenw espw,
  pinvG m eb el errw hackw posw entpw clenw espw -> munch W m m' -> wmono asegs m m' ->
  (forall X n, (P <= X /\ X + n <= P + 504) \/ (0 <= X /\ X + n <= 0x609000) -> disjoint_from W X n) ->
  pinvG m' eb el errw hackw posw entpw clenw espw.
Proof.
  intros W m m' eb el errw hackw posw entpw clenw espw (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC) MU WM DJ.
  assert (TR : forall X cs, rw_cells asegs m X cs -> ((P <= X /\ X + Z.of_nat (cells_size cs) <= P + 504) \/ (0 <= X /\ X + Z.of_nat (cells_size cs) <= 0x609000)) -> rw_cells asegs m' X cs)
    by (intros X cs H HR; eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; exact HR]).
  unfold pinvG. unfold llist_cells, mbuf_cells in *.
  split; [apply TR; [exact PM| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PRS| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [exists pad; apply TR; [exact PV| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PL| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PE| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PMB| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PC| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PS| left; cbn [cells_size csize Nat.add]; lia]|].
  split; [exists ev; apply TR; [exact PERR| right; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PGOT| right; cbn [cells_size csize Nat.add]; lia]|].
  split; [apply TR; [exact PCAN| right; cbn [cells_size csize Nat.add]; lia]|].
  apply TR; [exact PIWC| right; cbn [cells_size csize Nat.add]; lia].
Qed.

#[using="lo m0 A cur RF0 ARNG PLB"] Lemma pinv_dj_F : forall a b, F <= a -> b <= F + 512 -> forall X n, (P <= X /\ X + n <= P + 504) \/ (0 <= X /\ X + n <= 0x609000) -> disjoint_from [(a, b)]%Z X n.
Proof.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros a b H1 H2 X n HR. cbn [disjoint_from]. split; [| exact I]. clear - H1 H2 HR PFAP GF1 FSB1. lia.
Qed.
#[using="lo m0 A cur RF0 ARNG PLB"] Lemma pinv_dj_SF : forall X n, (P <= X /\ X + n <= P + 504) \/ (0 <= X /\ X + n <= 0x609000) -> disjoint_from [(SF, SF + 64)]%Z X n.
Proof.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  intros X n HR. cbn [disjoint_from]. split; [| exact I]. clear - HR ESF ESHB EKF EKB GF1 GF2 PFS1 PFS2 FSB1 FSB2 FSB5 ACR. lia.
Qed.
#[using="HC CLO PHI"] Lemma pinv_dj_stk : forall a b, lo <= a -> forall X n, (P <= X /\ X + n <= P + 504) \/ (0 <= X /\ X + n <= 0x609000) -> disjoint_from [(a, b)]%Z X n.
Proof.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  intros a b H1 X n HR. cbn [disjoint_from]. split; [| exact I]. clear - H1 HR CLO PHI ACR. lia.
Qed.

#[using="P lo m0 A cur RF0 ARNG PLB"] Lemma shwE_now : forall m w2 w3, rw_cells asegs m SF (gshadow 0 w2 w3) -> shw m (F + 32) 8.
Proof.
  intros m w2 w3 SHF.
  destruct geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (FAL : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (rw_cells asegs m (sh F) (shadow_cells [241; 241; 241; 241; 0; 242; 242; 242; w2; w2; w2; w2; w2; w2; w2; w2; w2; w2; w2;
            242; 242; 242; 242; 242; w3; w3; w3; w3; w3; w3; w3; w3; w3; w3; w3; 243; 243; 243; 243; 243;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) in SHF.
  assert (S32 : sh (F + 32) = sh F + 4) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (S287 : sh (F + 32 + 8 - 1) = sh F + 4) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (SM : sh F mod 8 = 0) by (unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia).
  split; [| split].
  - apply (accessible_of_chunk m F _ (F + 32) 8 SHF FAL); [lia| cbn [length]; lia|].
    intros i Hi H1 H2. cbn [length] in Hi.
    do 5 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). exfalso. lia.
  - apply (sh_readable_of_chunk m F _ (F + 32) 8 SHF).
    + rewrite S32. clear - SM. Z.div_mod_to_equations. lia.
    + rewrite S287. cbn [length]. clear - SM. Z.div_mod_to_equations. lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. lia.
Qed.

#[using="Type"] Lemma sub_fp_WPg : forall VWc, sub_fp WPg (W0c VWc).
Proof. intros VWc xo Ho. cbn [outside app] in *. destruct Ho as (_ & _ & _ & H4 & H5 & H6 & _). split; [exact H4|]. split; [exact H5|]. split; [exact H6| exact I]. Qed.

#[using="IC kq kP CLO LO AL16 Q63 RF0 PAL PLO PHI SHWP SHWERR TPV ARNG PLB HPURE"] Lemma blockDf : forall VWc (h : hv) q' m v24 v32 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31,
  In h hvs -> vw_ok VWc -> minvG VWc q' m 248 0 248 v24 v32 -> pinvG m eb el errw hackw posw entpw clenw espw -> hview m ->
  forall (Q : machine_state -> Prop),
  (forall m' clenw' v24' v32' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y25 y28 y29 y30 y31,
     minvG VWc q' m' 248 248 248 v24' v32' ->        pinvG m' eb el errw hackw posw (wz 2) clenw' espw -> hview m' ->
     evt asegs Q (GSTP 0x89730 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 6) y21 y22 y25 y28 y29 y30 y31 m')) ->
  evt asegs Q (GSTP 0x899dc q' x1 x5 x6 x7 (Z_to_bv 64 (hvN h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 (Z_to_bv 64 (P + 288)) x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros Hh VWOK INV PINV HV Q K.
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
  clear SE0 RU1 RU2.
  destruct (HPURE h Hh) as (LC & CAPB & RN & RI & RV). unfold H_germ_seg1.hreg in RN, RI, RV.
  destruct (lsegA_node _ _ _ _ _ (hvN h) (hvIt h) (hvId h) LS ltac:(apply in_map_iff; exists h; split; [reflexivity| exact Hh])) as (pv' & nx & NC).
  unfold node_cells in NC. unfold mbuf_cells in VC.
  assert (SHWEs : shw m ERRNO_G 4) by (eapply (shw_frame_fs FI (W0c VWc) m0 m); [exact SHWERR| exact MU| exact (W0c_fsw VWc VWOK)| left; clear - FSB1; lia]).
  pose proof AE as AEs.
  hideW MU WM.
  pose proof (munch_refl [(lo, q' + 40); (SF, SF + 64); (F + 32, F + 40); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  assert (HSD : hsafeW [(lo, q' + 40); (SF, SF + 64); (F + 32, F + 40); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)]%Z).
  { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [left; cbn [fst]; exact CLO|].
    apply Forall_cons; [right; right; left; cbn [fst snd]; clear - ESF ESHB EKF EKB GF1 GF2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - GF1 GF2; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|].
    apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia| apply Forall_nil]. }
  step. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ RN ACR. lia. } clear KZ.
  walk_ub_to 0x89a28.
  cstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHI1 : shw mm (hvIt h) 88) by (eapply (shw_frame_fs FI _ m mm); [exact SHI| exact MU0| exact (proj1 HSD)| clear - RI; lia]) end.
  walk_ub_to 0x89a48. clear SHI1.

  clear N1 N2 N3 I1 I2 I3 RN RI SHN SHI. try clear NC. try clear VC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 12 sstep.
  unhide_transport MUs WMs. clear MUs WMs.
  step. step. if_cases KL; zify_cond KL. { exfalso. clear - KL LC CAPB. lia. } clear KL.
  step.
  assert (TPU : bv_unsigned tp - 164 = 6190348) by (rewrite TPV; rewrite unsigned_lit by lia; reflexivity).
  eapply evt_cut; [eapply (ic_errno_location IC); [clear - TPU; lia| eassumption]|].
  intros msE PE0. unfold leaf_post in PE0. destruct PE0 as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & -> & _ & _ & _).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  rewrite TPU.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHWE2 : shw mm ERRNO_G 4) by (eapply (shw_frame_fs FI _ m mm); [exact SHWEs| exact MU0| exact (proj1 HSD)| left; clear - FSB1; lia]) end.
  walk_ub_to 0x89a98.
  chkwN 11 6190348 4 SHWE2 kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]]; [| exfalso; change (6190348 mod 8) with 4 in G2; clear - G1 G2; lia].
  step. step. lit_branch.
  walk_lia_to 0x441b4.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  assert (SHVc : shw mc (hvA h) (hvCap h + 1)) by (eapply (shw_frame_fs FI _ m mc); [exact SHV| exact MU0| exact (proj1 HSD)| clear - RV; lia]).
  pose proof (shwE_now mc _ _ SHF) as SHEc.
  pose proof VN as VN2. apply List.nth_error_split in VN2 as (str & vrest & EV & LSTR).
  assert (BYS : bytes_at asegs mc (hvA h) (str ++ [zbG])).
  { destruct VB as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. rewrite EV in BY.
    replace (str ++ zbG :: vrest) with ((str ++ [zbG]) ++ vrest) in BY by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BY. exact (proj1 BY). }
  assert (LS1 : Z.of_nat (length str) + 1 = hvLen h + 1) by (clear - LSTR LC; lia).
  destruct (shw_sub _ _ _ (hvA h) (hvLen h + 1) SHVc ltac:(lia) ltac:(clear - LC; lia) ltac:(clear - LC; lia)) as (ACS & RDS & _).
  destruct SHEc as (ACE & RDE & _).
  assert (TPE : bv_unsigned tp = 6190512) by (rewrite TPV; apply unsigned_lit; lia).
  env_sync AE MU0 WM0.
  eapply evt_cut.
  { eapply (ic_strtoll IC) with (S := hvA h) (str := str) (E := F + 32) (ejunk := je) (canary := canary) (lo := lo) (q := q');
      [ exact BYS | exact LE | rewrite TPU; exact PERR | exact PGOT | exact PCAN | exact AE
      | rewrite LS1; exact ACS | rewrite LS1; exact RDS | unfold icpt_win; clear - LS1 LC RV ACR; lia | clear - LS1 LC CAPB; lia
      | exact ACE | exact RDE | unfold icpt_win; clear - GF1 GF2 FSB1 FSB2 FSB5 ACR; lia
      | exact ST | exact CLO | unfold A0_STRTOL_DEPTH; clear - LO Hq; lia | clear - Q63 Hq; lia
      | clear - TPE; lia | clear - TPE; lia | exact TPE
      | clear - RV; lia | clear - RV LS1 LC; lia | clear - GF1 FSB1; lia | clear - GF2 FSB2; lia | clear - EKF; Z.div_mod_to_equations; lia
      | clear - RV GF1 GF2 LS1 LC; lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros msS PS0. unfold strtol_post_A in PS0.
  destruct PS0 as (u0 & u1 & u2 & rv & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & kk & -> & MUc & WMc & MI' & ST' & AE' & BYS' & PGOT' & PCAN' & PERR' & KK & LE').
  clear BYS ACS RDS ACE RDE SHVc MI ST AE PGOT PCAN.
  transport_after_call asegs mc m' MUc WMc.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  rewrite TPU in PERR'.
  step. step.
  clear MUc WMc. unfold A0_got_ssp in PGOT'. unfold A0_ssp_guard in PGOT', PCAN'.
  assert (J : forall y10 y11 y12 y13 y25, evt asegs Q (GSTP 0x89af8 q' (Z_to_bv 64 563900) u0 u1 u2 y10 y11 y12 y13 u7 u8 u9 u10 (Z_to_bv 64 P) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (-8)) y25 u11 u12 u13 u14 m')).
  { intros y10 y11 y12 y13 y25.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
    pose proof (hview_frame _ m mZ HV MU0 WM0 HSD) as HVZ.
    assert (SUBD : sub_fp [(lo, q' + 40); (SF, SF + 64); (F + 32, F + 40); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)]%Z (W0c VWc)).
    { intros xo Ho. cbn [outside app] in *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _).
      split; [clear - H1 Hq; lia|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [clear - H2 GF1 GF2; lia|]. split; [exact H5|]. split; [exact H6| exact I]. }
    absorbW MU WM MU0 WM0 SUBD.
    env_sync AEs MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    pose proof (shwP_now mZ FK) as SHWPs.
    pose proof (munch_refl WPg mZ) as MU0. pose proof (wmono_refl asegs mZ) as WM0.
    hideW MU WM.
    wPA SHWPs MU0 SHWPn 0x89730.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mK end.
    assert (HSP : hsafeW WPg).
    { apply hsafe_of. unfold hsafe_iv. apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|]. apply Forall_cons; [right; right; right; cbn [fst snd]; clear; lia| apply Forall_nil]. }
    pose proof (hview_frame _ mZ mK HVZ MU0 WM0 HSP) as HVK.
    pose proof (sub_fp_WPg VWc) as SUBW.
    absorbW MU WM MU0 WM0 SUBW. env_sync AEs MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    destruct (rw_cells_forget asegs _ _ _ LE') as (je' & LEc). cbn [cells_size csize Nat.add] in LEc. clear LE'.
    rename AEs into AE.
    eapply K; [mv_tacG| pv_tacG| exact HVK].
  }
  if_cases KR; zify_cond KR; [apply J|]. clear KR.
  walk_ub_to 0x89af8.
  apply J.
Qed.

End W.
