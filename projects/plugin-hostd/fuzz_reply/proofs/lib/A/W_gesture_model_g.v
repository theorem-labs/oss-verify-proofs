(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: gesture_model at its caller's choice of globals (W_contract.v gm_spec_g), the
   composition of lane W4's three cuts with the callees' G-generic contracts:
     pb_gesture_model (W_gesture_model.v, entry to the scan loop, GMSCAN open)
     gm_scan          (W_gm_scan.v, the scan loop 0x85c18, GMFOUND open)
     gm_found         (W_gm_found.v, the found point 0x85c58 to the return / tail calls)
   and, at the caller's G: list_find by lfind_spec_g (lane W1), list_push by lp_spec_g (lane W2), list_drop by
   W1's pb_list_drop_ro statement (W_list_drop_top.v: any G with gx_ok, gx_rt and rom_out).
   ARx conversion (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): Section c proves pb_gesture_model_g_x : gm_spec_g_x
   over a generic allocator relation ARx from the three cuts' _x theorems (pb_gesture_model_x, pb_gm_scan_x,
   pb_gm_found_x) and the callees' _g_x twins; Section r re-derives pb_gesture_model_g, statement unchanged, at
   ARx := W_journal_x.ARi0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_gesture_model W_gm_scan W_gm_found.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfParamsReply AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_shadow_pin_x.
(* image A's PAImg instance (W_img.v:58), taken qualified so the generic Sections above keep their own PI *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* ---- THE GENERIC COMPOSITION (route (b), step 3): over any allocator relation ARx with its laws (LAWS) and no hidden
   head (HP0, a Theorem Labs lane's ruling); the callees are their _g_x twins at the same PST / ARx. ---- *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
(* the room round (W_contract_x.v Section w4g): the room parameter, after MT as the kit's spec Sections take it *)
Variable RP : roomp.
Variable MMAX : Z.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
(* the three literals are addressable with a visible shadow hull in every ARx state (W_shadow_pin.v ashp over ARx,
   W_contract_x.ashp_x; at the AR instance W_shadow_pin_fr.v ashp_gesture_13_fr / ashp_begin_5_fr / ashp_end_3_fr). *)
Hypothesis HLITG : ashp_x ARx (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp_x ARx (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp_x ARx (VAL A_lit_end) 3.
(* the callees at the caller's G *)
Hypothesis LFIND_G : lfind_spec_g_x B PST ARx (BASE + AF_fr_list_find).
Hypothesis LPUSH_G : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_RO : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).

Theorem pb_gesture_model_g_x : gm_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_gesture_model).
Proof.
intros G HG GRT HRO.
pose proof (LFIND_G G HG GRT) as LFIND. pose proof (LPUSH_G G HG GRT) as LPUSH.
pose proof (LDROP_RO G HG GRT HRO) as LDROP.
eapply W_gesture_model.pb_gesture_model_x; try eassumption.
intros. eapply W_gm_scan.pb_gm_scan_x; try eassumption.
intros. eapply W_gm_found.pb_gm_found_x; eassumption.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the composition at a world relation R.  The entry walk is
   W_gesture_model.pb_gesture_model_xR, the scan loop W_gm_scan.pb_gm_scan_xR, the found point W_gm_found.pb_gm_found_xR
   (a Theorem Labs lane's); the statement is W_contract_xR_g6.gm_spec_g_xR.  list_push and list_drop are taken at R at the
   caller's G (LPUSH_G_R, LDROP_RO_R); list_find stays strict (LFIND_G).  The strict texts above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the list callees at the caller's G, at R (W_contract_xR.lp_spec_g_xR, W_contract_xR_g3.ldrop_spec_xR): what
   W_gm_found.pb_gm_found_xR takes as LPUSH_R / LDROP_R *)
Hypothesis LPUSH_G_R : lp_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_RO_R : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec_xR B PST ARx R MT RP G (BASE + AF_fr_list_drop).
(* :82 pb_gesture_model_g_x *)
Theorem pb_gesture_model_g_xR : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Proof.
intros G HG GRT HRO.
pose proof (LFIND_G G HG GRT) as LFIND.
pose proof (LPUSH_G_R G HG GRT) as LPUSH_R. pose proof (LDROP_RO_R G HG GRT HRO) as LDROP_R.
eapply W_gesture_model.pb_gesture_model_xR; try eassumption.
intros. eapply W_gm_scan.pb_gm_scan_xR; try eassumption.
intros. eapply W_gm_found.pb_gm_found_xR; eassumption.
Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): pb_gesture_model_g's statement is the AR
   composition's, unchanged, now a corollary of pb_gesture_model_g_x at ARx := ARi0, PST := [] through W_contract_x
   gm_spec_g_x_AR0.  LX0 replaces LAWS; HP0 at ARi0 is ARi0_hp0; the callees' AR contracts become their generic ones
   at ARi0 through the kit's bridges (W_contract_x lfind_spec_g_x_of_AR0 / lp_spec_g_x_of_AR0 / ldrop_spec_x_of_AR0 /
   ashp_x_ARi0_of, W_sites_x abcmp_realizes_x_of_AR0). ---- *)
Section r.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis HLITG : ashp B (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp B (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp B (VAL A_lit_end) 3.
Hypothesis LFIND_G : lfind_spec_g B (BASE + AF_fr_list_find).
Hypothesis LPUSH_G : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_RO : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec B MT G (BASE + AF_fr_list_drop).

Theorem pb_gesture_model_g : gm_spec_g B MT MMAX (BASE + AF_fr_gesture_model).
Proof.
apply gm_spec_g_x_AR0.
pose proof (ARi0_hp0 SEGS B) as HP0.
pose proof (abcmp_realizes_x_of_AR0 SEGS B _ ABCMP) as ABCMPx.
pose proof (ashp_x_ARi0_of B _ _ HLITG) as HLITGx. pose proof (ashp_x_ARi0_of B _ _ HLITB) as HLITBx.
pose proof (ashp_x_ARi0_of B _ _ HLITE) as HLITEx.
pose proof (lfind_spec_g_x_of_AR0 B _ LFIND_G) as LFIND_Gx.
pose proof (lp_spec_g_x_of_AR0 B _ _ _ LPUSH_G) as LPUSH_Gx.
assert (LDROP_ROx : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
  ldrop_spec_x B [] (ARi0 SEGS B) MT RP_AR G (BASE + AF_fr_list_drop))
by (intros G H1 H2 H3; apply ldrop_spec_x_of_AR0; exact (LDROP_RO G H1 H2 H3)).
eapply (pb_gesture_model_g_x B MT RP_AR MMAX [] (ARi0 SEGS B)); eassumption.
Qed.
End r.
End b.
End a.

(* ---- AT top_x's INSTANCE (for top_x's CSE_x / CNL_x / CSHE_x discharges). gesture_model's _g_x
   contract at TfibB, PST := [] and top_x's allocator relation ARX (W_LLVMFuzzerTestOneInput_top_x.v Definition ARX,
   spelled out here so that top_x can Require this file: ARX unfolds to it), MMAX := fr_MMAX.  The relation's laws and
   no-hidden-head are discharged as top_x's ARX_laws / ARX_hp0 prove them, and the three literals' shadow facts by
   W_shadow_pin_x (for every ARx with AR_laws_x and every B with TfibSyms B, decided by vm_compute over the start-up
   tables).  The meter MT and the room parameter RP stay the caller's; bcmp's RT realization at ARX (ABCMP) and the
   three list callees' contracts are named hypotheses, at ARX. ---- *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head.
#[local] Notation segs := (@pa_segs _ fr_prog_listing W_img.PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing W_img.PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing W_img.PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing W_img.PB_fr A_TEXT).
(* top_x's ARX, word for word *)
Local Notation ARXc := (fun ly S Hp (W : world segs) mem md =>
  ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []).
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis TL : PALib TfibB.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x segs TfibB ARXc (SIGMA WS_bcmp).
Hypothesis LFIND_G : lfind_spec_g_x TfibB [] ARXc (BASE + AF_fr_list_find).
Hypothesis LPUSH_G : lp_spec_g_x TfibB [] ARXc MT RP CfParamsReply.fr_MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_RO : forall G, gx_ok segs TfibB G -> gx_rt TfibB G -> rom_out segs TfibB G ->
  ldrop_spec_x TfibB [] ARXc MT RP G (BASE + AF_fr_list_drop).
Theorem pb_gesture_model_g_cf :
  gm_spec_g_x TfibB [] ARXc MT RP CfParamsReply.fr_MMAX (BASE + AF_fr_gesture_model).
Proof.
  assert (LAWS : AR_laws_x segs TfibB ARXc (@cf_head CfParams_reply)).
  { apply AR_laws_x_and_hp.
    exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)). }
  assert (HP0 : forall ly S Hp (W : world segs) mem md, ARXc ly S Hp W mem md -> Hp = [])
    by (intros ly S Hp W mem md H; exact (proj2 H)).
  pose proof (W_shadow_pin_x.ashp_gesture_13_fr_x TfibB TfibB_syms ARXc LAWS) as HLITG.
  pose proof (W_shadow_pin_x.ashp_begin_5_fr_x TfibB TfibB_syms ARXc LAWS) as HLITB.
  pose proof (W_shadow_pin_x.ashp_end_3_fr_x TfibB TfibB_syms ARXc LAWS) as HLITE.
  eapply pb_gesture_model_g_x; eassumption.
Qed.
(* route R: pb_gesture_model_g_cf at a world relation R, from pb_gesture_model_g_xR; LPUSH_G_R_cf / LDROP_RO_R_cf are
   Section b's LPUSH_G_R / LDROP_RO_R at this instance *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Hypothesis LPUSH_G_R_cf : lp_spec_g_xR TfibB [] ARXc R MT RP CfParamsReply.fr_MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_RO_R_cf : forall G, gx_ok segs TfibB G -> gx_rt TfibB G -> rom_out segs TfibB G ->
  ldrop_spec_xR TfibB [] ARXc R MT RP G (BASE + AF_fr_list_drop).
(* :157 pb_gesture_model_g_cf *)
Theorem pb_gesture_model_g_cf_xR :
  gm_spec_g_xR TfibB [] ARXc R MT RP CfParamsReply.fr_MMAX (BASE + AF_fr_gesture_model).
Proof.
  assert (LAWS : AR_laws_x segs TfibB ARXc (@cf_head CfParams_reply)).
  { apply AR_laws_x_and_hp.
    exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)). }
  assert (HP0 : forall ly S Hp (W : world segs) mem md, ARXc ly S Hp W mem md -> Hp = [])
    by (intros ly S Hp W mem md H; exact (proj2 H)).
  pose proof (W_shadow_pin_x.ashp_gesture_13_fr_x TfibB TfibB_syms ARXc LAWS) as HLITG.
  pose proof (W_shadow_pin_x.ashp_begin_5_fr_x TfibB TfibB_syms ARXc LAWS) as HLITB.
  pose proof (W_shadow_pin_x.ashp_end_3_fr_x TfibB TfibB_syms ARXc LAWS) as HLITE.
  eapply pb_gesture_model_g_xR; eassumption.
Qed.
End wR.
End cf.
