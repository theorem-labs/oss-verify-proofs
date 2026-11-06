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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF F_ctypeA H_parse_uric H2Kit AWRng AWUb.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_memptr_cmp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import H_puri_seg1.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (U O ulen lo q kq kO : Z) (ustr slack : list byte) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
Variable canary : word.

Local Notation F := (puriF FI st).  Local Notation FL := (puriFL FI st).  Local Notation SF := (puriSF FI st).  Let st1 := fs_next FI st 3.

Notation WP := [(O, O + 216); (ERRNO_A, ERRNO_A + 4)]%Z.
Notation W0 := ((lo, q) :: FSIV WP)%Z.

Notation ushadow w :=
  ([C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).

Notation USTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 SF) (Z_to_bv 64 U) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Notation zbU := (Z_to_bv 8 0).

Local Notation minvU := (H_puri_seg1.minvU FI O lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
Local Notation UBANDd := (H_puri_seg1.UBANDd U ulen slack).
Local Notation pinvR := (H_puri_seg1.pinvR U ustr slack canary).
Local Notation pinvU := (H_puri_seg1.pinvU U O ustr slack canary).
Local Notation WEU := (H_puri_seg1.WEU FI lo q st).
Local Notation rframeU := (H_puri_seg1.rframeU FI lo q st).
Local Notation postU := (H_puri_seg1.postU FI O lo q st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0).
Local Notation XU := (H_puri_seg1.XU U O ustr slack canary).

Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - PURI_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^63.
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 1.
Hypothesis FE0 : FSENV FI m0.
Hypothesis Q47 : q <= 2^47 - 64.
Hypothesis SHZ : shz m0 (sh lo) (sh q).
Hypothesis SHR : shr m0 (sh lo - sh lo mod 8) (sh q + 8).

Hypothesis OAL : O = 8 * kO.
Hypothesis OLO : 0x609000 <= O.
Hypothesis OHI : O + 216 <= alloc_ceiling.
Hypothesis OLB : lb (fs_live FI st) O 216.
Hypothesis SHWO : shw m0 O 216.
Hypothesis ULEN : Z.of_nat (length ustr) = ulen.
Hypothesis ULR : 0 <= ulen < 2^31.
Hypothesis PAD : (- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis UIMG : 0x609000 <= U.
Hypothesis UHI : U + ulen + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Hypothesis UFS : U + ulen + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U.
Hypothesis UBAND : UBANDd.
Hypothesis SHWU : shw m0 U (ulen + 1).
Hypothesis SHWHTTPS : shw m0 HTTPS_A 6.
Hypothesis SHWGIF : shw m0 GIF_A 4.
Hypothesis SHWMARK : shw m0 MARKTAB_A 10.
Hypothesis SHWRESV : shw m0 RESVTAB_A 13.
Hypothesis TPV : tp = Z_to_bv 64 6190512.

Local Notation geomU := (H_puri_seg1.geomU FI U O ulen lo ustr slack st m0 RF0 OLB ULR).
Local Notation prologueU := (H_puri_seg1.prologueU FI STACK_MALLOC_3 U O ulen lo q kq ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 CLO LO AL16 QHI RF0 FCO FE0 Q47 OHI OLB ULR).
Local Notation WP_app := (H_puri_seg1.WP_app U O ulen lo ustr slack m0 SHWO ULR).
Local Notation W0_fsw := (H_puri_seg1.W0_fsw FI U O ulen lo q ustr slack m0 CLO SHWO ULR).
Local Notation shwStk_now := (H_puri_seg1.shwStk_now FI U O ulen lo q kq ustr slack m0 CLO LO AL16 Q47 SHZ SHR SHWO ULR).
Local Notation WP_out := (H_puri_seg1.WP_out FI U O ulen lo ustr slack m0 SHWO ULEN ULR PAD UHI).
Local Notation shwO_now := (H_puri_seg1.shwO_now FI U O ulen lo q ustr slack st m0 RF0 OLB SHWO ULEN ULR PAD UHI).
Local Notation shwU_now := (H_puri_seg1.shwU_now FI U O ulen lo q ustr slack m0 CLO SHWO ULR UFS SHWU).
Local Notation shwG_now := (H_puri_seg1.shwG_now FI U O ulen lo q ustr slack m0 CLO SHWO ULR).
Local Notation liveU := (H_puri_seg1.liveU FI U O ulen lo ustr slack st m0 RF0 OLB ULR).
Local Notation sub_fp_O := (H_puri_seg1.sub_fp_O FI U O ulen lo q ustr slack ULR).
Local Notation sub_fp_cons2 := (H_puri_seg1.sub_fp_cons2 FI U ulen slack ULR UFS).
Local Notation sub_fp_stk := (H_puri_seg1.sub_fp_stk FI U O ulen lo q ustr slack ULR).
Local Notation out_open := (H_puri_seg1.out_open U O ulen lo ustr slack ULR).
Local Notation out_close := (H_puri_seg1.out_close U O ulen lo ustr slack ULR).
Local Notation memsetO := (H_puri_seg1.memsetO FI IC U O ulen lo q kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UHI UFS).
Local Notation memsetOo := (H_puri_seg1.memsetOo FI IC U O ulen lo q kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UHI UFS).
Local Notation sub_fp_WEU := (H_puri_seg1.sub_fp_WEU FI U O ulen lo q ustr slack st m0 RF0 OLB ULR).
Local Notation exitU := (H_puri_seg1.exitU FI SET_SHADOW_F5 U O ulen lo q kq ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 CLO LO AL16 RF0 Q47 OLB ULEN ULR PAD UHI).
Local Notation puricO := (H_puri_seg1.puricO FI IC U O ulen lo q kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS SHWU SHWMARK SHWRESV).
Local Notation WEU_dj_O := (H_puri_seg1.WEU_dj_O FI U O ulen lo q ustr slack st m0 CLO RF0 OHI OLB ULR).
Local Notation WEU_dj_U := (H_puri_seg1.WEU_dj_U FI U O ulen lo q ustr slack st m0 CLO RF0 OLB ULR UHI UFS UBAND).
Local Notation WEU_dj_low := (H_puri_seg1.WEU_dj_low FI U O ulen lo q ustr slack st m0 CLO RF0 OLB ULR).
Local Notation pinvR_rframe := (H_puri_seg1.pinvR_rframe FI U O ulen lo q ustr slack st m0 canary CLO RF0 OLB ULEN ULR UHI UFS UBAND).
Local Notation XU_rframe := (H_puri_seg1.XU_rframe FI U O ulen lo q ustr slack st m0 canary CLO RF0 OHI OLB ULEN ULR UHI UFS UBAND).
Local Notation tail2U := (H_puri_seg1.tail2U FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation slti0_nonnegU := (H_puri_seg1.slti0_nonnegU U ulen lo ustr slack ULR).
Local Notation Z_to_le_bytes_appU := (H_puri_seg1.Z_to_le_bytes_appU U ulen lo ustr slack ULR).
Local Notation le8_small_splitU := (H_puri_seg1.le8_small_splitU U ulen lo ustr slack ULR).
Local Notation rw_cells_C8_C4C4U := (H_puri_seg1.rw_cells_C8_C4C4U FI U ulen lo ustr slack ULR UFS).
Local Notation rw_cells_C4C4_C8U := (H_puri_seg1.rw_cells_C4C4_C8U FI U ulen lo ustr slack ULR UFS).
Local Notation tailU := (H_puri_seg1.tailU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation nohpU := (H_puri_seg1.nohpU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).

Ltac mv_tacU := unfold H_puri_seg1.minvU; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Ltac pr_tacU := unfold H_puri_seg1.pinvR; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption| eexists; eassumption].
Ltac pv_tacU := unfold H_puri_seg1.pinvU; split; [eassumption| pr_tacU].

Ltac ub_ptr := rewrite ?slti0_nonnegU by lia; ub_b2z; cbn [Z.b2z]; change (Z.lxor (Z.lxor 0 0) 1) with 1.

Notation XOK := (XU (fun r => r = 1)).

Notation XALL := (XU (fun r => r = 1 \/ r = -108)).

#[using="Type"] Lemma postU_mono : forall (X Y : Z -> mem -> Prop) ms, (forall r m, X r m -> Y r m) -> postU X ms -> postU Y ms.
Proof.
  intros X Y ms H (r & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & P).
  exists r, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st'. split; [exact E|].
  destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9). repeat (split; [assumption|]). apply H. exact P9.
Qed.
#[using="Type"] Lemma XOK_ALL : forall r m, XOK r m -> XALL r m.
Proof. intros r m (E & J). split; [left; exact E| exact J]. Qed.

#[using="U ulen ustr slack CLO RF0 OLB ULR"] Lemma stackcallU : forall q' m m' w v0 v8 v16 v24 v32 v40 v48 v56 wb,
  minvU q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb -> munch [(lo, q')]%Z m m' -> wmono asegs m m' ->
  mem_inv asegs m' -> stk asegs m' lo q' -> asan_env asegs m' ->
  minvU q' m' w v0 v8 v16 v24 v32 v40 v48 v56 wb.
Proof.
  intros until wb. intros INV MUc WMc MI' ST' AE'.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  hideW MU WM.
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear ST AE MI.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_stk lo q' ltac:(lia) ltac:(lia)).
  clear MUt WMt.
  mv_tacU.
Qed.
#[using="CLO"] Lemma stack_dj : forall q' X n, q + -208 <= q' <= q + -192 -> X + n <= alloc_ceiling -> disjoint_from [(lo, q')]%Z X n.
Proof. intros q' X n Hq H. cbn [disjoint_from]. split; [left; clear - H CLO; lia| exact I]. Qed.
#[using="HC ulen CLO ULEN ULR UHI"] Lemma pinvR_stack : forall q' m m', q + -208 <= q' <= q + -192 -> pinvR m -> munch [(lo, q')]%Z m m' -> wmono asegs m m' -> pinvR m'.
Proof.
  intros q' m m' Hq (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)) MU WM. unfold pinvR.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  split; [apply (bytes_at_transport asegs _ m m' _ _ TXT MU); apply (stack_dj q' _ _ Hq); rewrite length_app; cbn [length]; lia|].
  split; [exists ev; apply (rw_cells_transport asegs _ m m' _ _ ERRC MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m m' _ _ SSPG MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m m' _ _ SSPC MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m m' _ _ GOTG MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists gv. apply (rw_cells_transport asegs _ m m' _ _ GIFC MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.
#[using="HC U ulen ustr slack CLO OHI ULR"] Lemma out_stack : forall q' m m' junk, q + -208 <= q' <= q + -192 -> rw_cells asegs m O [CB 216 junk] -> munch [(lo, q')]%Z m m' -> wmono asegs m m' ->
  rw_cells asegs m' O [CB 216 junk].
Proof. intros q' m m' junk Hq OUT MU WM. apply (rw_cells_transport asegs _ m m' _ _ OUT MU WM). apply (stack_dj q' _ _ Hq). cbn [cells_size csize Nat.add]. lia. Qed.

#[using="U O ulen lo ustr slack m0 RF0 OLB ULR"] Lemma shwW_now : forall m, rw_cells asegs m SF (ushadow 0) -> shw m (F + 32) 256.
Proof.
  intros m SHF.
  destruct geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (FAL : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (rw_cells asegs m (sh F) (shadow_cells [241; 241; 241; 241;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
            243; 243; 243; 243; 243; 243; 243; 243;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) in SHF.
  assert (S32 : sh (F + 32) = sh F + 4) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (S287 : sh (F + 32 + 256 - 1) = sh F + 35) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (SM : sh F mod 8 = 0) by (unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia).
  split; [| split].
  - apply (accessible_of_chunk m F _ (F + 32) 256 SHF FAL); [lia| cbn [length]; lia|].
    intros i Hi H1 H2. cbn [length] in Hi.
    do 36 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). exfalso. lia.
  - apply (sh_readable_of_chunk m F _ (F + 32) 256 SHF).
    + rewrite S32. clear - SM. Z.div_mod_to_equations. lia.
    + rewrite S287. cbn [length]. clear - SM. Z.div_mod_to_equations. lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. lia.
Qed.

#[using="U ulen ustr slack m0 RF0 OLB ULR"] Lemma sub_fp_SF : sub_fp [(SF, SF + 64)]%Z W0.
Proof.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I].
Qed.

#[using="SET_SHADOW_F5 ulen kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB ULEN ULR PAD UHI UFS UBAND"] Lemma failU : forall q' m v0 v8 v16 v24 v32 v40 v48 v56 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvU m junk ->
  evt asegs (postU XALL)
    (USTP 0x8df74 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  hideW MU WM.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  step.
  do 32 sstep.
  unhide_transport MUs WMs.
  absorbW MU WM MUs WMs sub_fp_SF.
  env_sync AE MUs WMs. fs_sync FI RF MUs WMs FK LSUB.
  clear UBu.
  step.   step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (exitU (-108) XALL q' mm 248 v0 v8 v16 v24 v32 v40 v48 v56 wb); [mv_tacU| split; [right; reflexivity| exists junk; pv_tacU]| apply XU_rframe] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma hpendU : forall (bp2 size : Z) q' m v24 v32 wb junk
    x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v24 v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen ->
  evt asegs (postU XALL)
    (USTP 0x8de7c q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 x24 x25 (Z_to_bv 64 (F + 32 + size)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP SZ BPS.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O + 64, O + 80)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  destruct (out_open m junk 64 16 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 64) with (O + 64) in O2.
  pose proof (munch_refl [(O + 64, O + 80)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step.
  step. step. step.
  chk8N 11 (O + 72) SHWO'. step. lit_branch.
  step.
  rewrite ?(unsigned_lit (F + 32 + size)), ?(unsigned_lit (F + 32)) by lia. replace (F + 32 + size - (F + 32)) with size by lia.
  step. step.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step.
  chk8N 12 (O + 64) SHWO1.
  step. lit_branch.
  step.
  step; fix_lit_store.
  step.   rewrite (unsigned_lit size) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 64) (O + 80) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear SHWO' SHWO1 AIV.

  hideW MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  step.
  do 32 sstep.
  unhide_transport MUs WMs.
  absorbW MU WM MUs WMs sub_fp_SF.
  env_sync AE MUs WMs. fs_sync FI RF MUs WMs FK LSUB.
  clear UBu.
  step.
  step.   if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?signed_of_Z by lia. rewrite ?unsigned_lit by lia. lia. }
  step.

  pose proof (rw_cells_C8_C4C4U _ q' [] bp2 _ QC ltac:(lia)) as QC'. clear QC. cbn [app] in QC'.
  step.
  pose proof (rw_cells_C4C4_C8U _ q' [] bp2 _ QC' ltac:(lia)) as QC. clear QC'. cbn [app] in QC.
  rewrite sx32_lit by lia. rewrite (unsigned_lit size) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
  zstep. zstep. rewrite swrap32_id by lia.
  step. ubr.
  step.
  step.   rewrite (unsigned_lit (size + bp2)) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
  step.
  zstep. ub_b2z. step. lit_branch_safe.
  replace (Z_to_bv 64 (size + bp2)) with (Z_to_bv 64 (bp2 + size)) by (f_equal; lia).
  replace (Z_to_bv 64 (U + (size + bp2))) with (Z_to_bv 64 (U + (bp2 + size))) by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 64 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    eapply evt_mono; [apply (tailU (bp2 + size) q' mm 248 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v24 v32 (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk'); [mv_tacU| split; [exact OUT'| pr_tacU]| lia]|] end.
  intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H).
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma inetU : forall (bp2 size af srv : Z) (off N : nat) (pre host rest : list byte) q' m v24 wb junk
    x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v24 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  ((af = 2 /\ off = 84%nat /\ N = 4%nat) \/ (af = 10 /\ off = 88%nat /\ N = 16%nat)) ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen ->
  evt asegs (postU XALL)
    (USTP 0x8de60 q' x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (Z.of_nat off - 64)) x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 af) x25 (Z_to_bv 64 (F + 32 + size)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL AF BP SZ BPS.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (HON : (off + N <= 216)%nat) by (destruct AF as [(_ & -> & ->)|(_ & -> & ->)]; lia).
  assert (OFR : (84 <= off <= 88)%nat /\ (4 <= N <= 16)%nat) by (destruct AF as [(_ & -> & ->)|(_ & -> & ->)]; lia).
  destruct (out_open m junk off N OUT HON) as (ja & jb & jc & O1 & O2 & O3). clear OUT.

  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  pose proof (bytes_at_bound _ _ _ _ WBB) as WBL.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  rewrite EWB in WBB. apply bytes_at_app in WBB. destruct WBB as [_ WBB]. rewrite <- ESRV in WBB.
  replace (host ++ Z_to_bv 8 0 :: rest) with ((host ++ [Z_to_bv 8 0]) ++ rest) in WBB by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in WBB. destruct WBB as [HOST _].
  assert (LH : Z.of_nat (length pre) + Z.of_nat (length host) + 1 <= 256).
  { rewrite EWB in LWB. rewrite !length_app in LWB. cbn [length] in LWB. lia. }
  assert (SHWW : shw m (F + 32) 256) by exact (shwW_now m SHF).
  assert (SHWh : shw m srv (Z.of_nat (length host) + 1)) by (apply (shw_sub m (F + 32) 256 _ _ SHWW); lia).
  assert (SHWo : shw m (O + Z.of_nat off) (Z.of_nat N)) by (apply (shwO_now m _ _ MU FK); lia).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (shwStk_now m q' MU Hq) as SHWS.
  hideW MU WM.
  step.
  step.   rewrite ?(unsigned_lit (O + 64)), ?(unsigned_lit (Z.of_nat off - 64)) by lia. replace (O + 64 + (Z.of_nat off - 64)) with (O + Z.of_nat off) by lia.
  step. step.
  step.
  eapply evt_cut.
  { eapply (ic_inet_pton IC) with (af := af) (S := srv) (A := O + Z.of_nat off) (str := host) (ojunk := jb) (N := N) (canary := canary) (lo := lo) (q := q');
    [ exact HOST | exact NONUL | exact O2 | destruct AF as [(-> & _ & ->)|(-> & _ & ->)]; [left| right]; split; [reflexivity| lia | reflexivity | reflexivity]
    | exact SSPG | exact SSPC
    | exact (proj1 SHWh) | exact (proj1 (proj2 SHWh)) | exact (proj2 (proj2 SHWh)) | lia
    | exact (proj1 SHWo) | exact (proj1 (proj2 SHWo)) | exact (proj2 (proj2 SHWo))
    | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
    | clear - Hq Q47; lia | exact (proj1 SHWS) | exact (proj1 (proj2 SHWS))
    | lia | lia | lia | lia | clear - ESRV PFAP OFR LH; lia
    | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold inet_pton_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & outs & -> & MUc & WMc & MI' & ST' & AE' & _ & _ & _ & _ & _ & O2' & R01).
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear O2 ST AE MI SHWW SHWh SHWo HOST SHWS.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) (sub_fp_O (O + Z.of_nat off) (O + Z.of_nat off + Z.of_nat N) ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 581236)) with (Z_to_bv 64 581236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  destruct (out_close m' off N _ _ _ O1 ltac:(cbn [cells_size csize Nat.add]; lia) O2' ltac:(cbn [cells_size csize Nat.add]; lia)
              O3 ltac:(cbn [cells_size csize Nat.add]; lia) HON) as [junk' OUT].
  step.
  step.   if_cases K0; zify_cond K0.
  - apply (failU q' m' (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v24 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk'); [mv_tacU| pv_tacU].
  - apply (hpendU bp2 size q' m' v24 (Z_to_bv 64 (F + 32)) wb junk'); [mv_tacU| pv_tacU| lia| lia| lia].
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma fam4U : forall (bp2 size port srv : Z) (pre host rest : list byte) q' m wb junk
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 port) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8dd98 q' x1 x5 x6 x7 (Z_to_bv 64 (O + 80)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 2) x25 (Z_to_bv 64 (F + 32 + size)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O + 80, O + 84)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  destruct (out_open m junk 80 4 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 80) with (O + 80) in O2.
  pose proof (munch_refl [(O + 80, O + 84)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step.
  chk8N 11 (O + 80) SHWO'. step. lit_branch.
  step.
  step.
  step; fix_lit_store.
  step.
  step. step.
  step.
  assert (H16 : forall x, bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48))) 48)) < 65536).
  { intros x. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia. }
  eapply evt_cut.
  { eapply (ic_htons IC); [exact (H16 port)| assumption]. }
  intros ms' PO. unfold leaf_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
  replace (ret_pc (Z_to_bv 64 581060)) with (Z_to_bv 64 581060) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 12 (O + 82) SHWO1. step. lit_branch.
  step; fix_lit_store.
  step.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 80) (O + 84) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO' SHWO1 AIV H16.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 80 4 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    apply (inetU bp2 size 2 srv 84 4 pre host rest q' mm (Z_to_bv 64 port) wb junk'); [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| left; repeat split| lia| lia| lia] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV"] Lemma fam6U : forall (bp2 size port srv : Z) (pre host rest : list byte) q' m wb junk
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 port) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8dde4 q' x1 x5 x6 x7 (Z_to_bv 64 (O + 80)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 10) x25 (Z_to_bv 64 (F + 32 + size)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O + 80, O + 108)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  destruct (out_open m junk 80 28 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  assert (SHWG0 : shw m GIF_A 4) by (apply (shwG_now m _ _ SHWGIF MU); lia).
  change (O + Z.of_nat 80) with (O + 80) in O2.
  pose proof (munch_refl [(O + 80, O + 108)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step.
  chk8N 11 (O + 80) SHWO'. step. lit_branch.
  step.
  step.
  step; fix_lit_store.
  step.
  step. step.
  step.
  assert (H16 : forall x, bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48))) 48)) < 65536).
  { intros x. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia. }
  eapply evt_cut.
  { eapply (ic_htons IC); [exact (H16 port)| assumption]. }
  intros ms' PO. unfold leaf_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
  replace (ret_pc (Z_to_bv 64 581136)) with (Z_to_bv 64 581136) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 12 (O + 82) SHWO1. step. lit_branch.
  step. step.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHWO2 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV);
    assert (SHWG : shw mm GIF_A 4) by exact (shw_frame _ m mm GIF_A 4 SHWG0 MU0 AIV) end.
  step. step.
  gen2 CONT 0x8de40 10%nat 12%nat.
  { intros yi yj.
    step. step. step.
    chk8N 12 (O + 104) SHWO2. step.   step. lit_branch.
    step; fix_lit_store.
    step.
    absorbW MU WM MU0 WM0 (sub_fp_O (O + 80) (O + 108) ltac:(lia) ltac:(lia)).
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    clear UBu SHWO' SHWO1 SHWO2 SHWG SHWG0 AIV H16.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 80 28 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
      apply (inetU bp2 size 10 srv 88 16 pre host rest q' mm (Z_to_bv 64 port) wb junk'); [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| right; repeat split| lia| lia| lia] end. }
  chkwN 10 718496 4 SHWG kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep. zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV"] Lemma portfamU : forall (bp2 size fam port srv : Z) (pre host rest : list byte) q' m wb junk
    x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 port) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 -> 0 <= fam < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8dd64 q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 fam) x25 (Z_to_bv 64 (F + 32 + size)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR FR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  destruct (out_open m junk 208 2 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 208) with (O + 208) in O2.
  pose proof (munch_refl [(O + 208, O + 210)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step.
  step. step. step.
  chk8N 11 (O + 208) SHWO'. step. lit_branch.
  step.
  step; fix_lit_store.
  step. step.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 208) (O + 210) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 208 2 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    assert (INV2 : minvU q' mm 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 port) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb) by mv_tacU;
    assert (PINV2 : pinvU mm junk') by pv_tacU end.
  step.   if_cases K1; zify_cond K1.
  { assert (fam = 10) by (revert K1; rewrite ?unsigned_lit by lia; lia). subst fam.
    lazymatch type of INV2 with minvU _ ?mm _ _ _ _ _ _ _ _ _ _ =>
      apply (fam6U bp2 size port srv pre host rest q' mm wb junk'); assumption end. }
  step.
  step.   if_cases K2; zify_cond K2.
  { lazymatch type of INV2 with minvU _ ?mm _ _ _ _ _ _ _ _ _ _ =>
      apply (hpendU bp2 size q' mm (Z_to_bv 64 port) (Z_to_bv 64 (F + 32)) wb junk'); assumption end. }
  assert (fam = 2) by (revert K2; rewrite ?unsigned_lit by lia; lia). subst fam.
  lazymatch type of INV2 with minvU _ ?mm _ _ _ _ _ _ _ _ _ _ =>
    apply (fam4U bp2 size port srv pre host rest q' mm wb junk'); assumption end.
Qed.

#[using="U ulen lo ustr slack ULR"] Lemma wb_nthU : forall (wb : list byte) i, length wb = 256%nat -> 0 <= i <= 255 -> exists b, nth_error wb (Z.to_nat i) = Some b.
Proof.
  intros wb i L Hi. destruct (nth_error wb (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

#[using="U ulen lo ustr slack ULR"] Lemma wb_decomp : forall (wb : list byte) (a z : Z), 0 <= a <= z ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j b, a <= j < z -> nth_error wb (Z.to_nat j) = Some b -> bv_unsigned b <> 0) ->
  exists pre s rest, wb = pre ++ s ++ zbU :: rest /\ Z.of_nat (length pre) = a /\ Z.of_nat (length s) = z - a /\ ~ In zbU s.
Proof.
  intros wb a z AZ WZ WNZ.
  destruct (nth_error_split _ _ _ WZ) as (l1 & l2 & E & L1).
  exists (firstn (Z.to_nat a) l1), (skipn (Z.to_nat a) l1), l2.
  split; [rewrite app_assoc, firstn_skipn; exact E|].
  split; [rewrite firstn_length_le by lia; lia|].
  split; [rewrite length_skipn; lia|].
  intros HIn. destruct (In_nth_error _ _ HIn) as [n Hn].
  assert (LN : (n < length (skipn (Z.to_nat a) l1))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  rewrite length_skipn in LN. rewrite nth_error_skipn in Hn.
  apply (WNZ (a + Z.of_nat n) zbU ltac:(lia)); [| reflexivity].
  rewrite E. rewrite nth_error_app1 by lia. replace (Z.to_nat (a + Z.of_nat n)) with (Z.to_nat a + n)%nat by lia. exact Hn.
Qed.
#[using="Type"] Lemma wb_strU : forall m (wb pre s rest : list byte), bytes_at asegs m (F + 32) wb -> wb = pre ++ s ++ zbU :: rest ->
  bytes_at asegs m (F + 32 + Z.of_nat (length pre)) (s ++ [zbU]).
Proof.
  intros m wb pre s rest WBB E. rewrite E in WBB. apply bytes_at_app in WBB. destruct WBB as [_ WBB].
  replace (s ++ zbU :: rest) with ((s ++ [zbU]) ++ rest) in WBB by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in WBB. exact (proj1 WBB).
Qed.

#[using="U O ulen lo ustr slack m0 RF0 OLB ULR"] Lemma wb_sh0 : forall m c (a : word), rw_cells asegs m SF (ushadow 0) -> 0 <= c <= 255 -> a = wa (sh (F + 32 + c)) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 0].
Proof.
  intros m c a SHF Hc Ha.
  pose proof (proj1 (shwW_now m SHF)) as ACC.
  destruct geomU as (kF & kB & EKF & _).
  apply (acc_load0 m (F + 32) 256 (F + 32 + c) a ACC); [clear - EKF Hc; Z.div_mod_to_equations; lia | clear - EKF Hc; Z.div_mod_to_equations; lia | exact Ha].
Qed.

Ltac chkW r c SHF HC :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHR := fresh "SHR" in
    assert (SHR : ov_read_bytes asegs mm a 1 = Some [Z_to_bv 8 0]) by (apply (wb_sh0 mm c a SHF HC); shadow_addr_tac) end;
  step; clear_shr.

#[using="U ulen lo ustr slack ULR"] Lemma wrap_sub_ltU : forall c a n, 0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
  Z.land (c + a) 18446744073709551615 < n -> - a <= c < - a + n.
Proof.
  intros c a n Hc Ha Hn H. change 18446744073709551615%Z with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases c (- a)).
  - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
#[using="U ulen lo ustr slack ULR"] Lemma wrap_sub_geU : forall c a n, 0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
  ~ (Z.land (c + a) 18446744073709551615 < n) -> ~ (- a <= c < - a + n).
Proof.
  intros c a n Hc Ha Hn H Hd. apply H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

#[using="U ulen ustr slack ULR"] Lemma sub_fp_errno : sub_fp [(ERRNO_A, ERRNO_A + 4)]%Z W0.
Proof. intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & _ & _ & H5 & _). split; [lia| exact I]. Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma portU : forall (bp2 p z fam srv : Z) (pre host rest : list byte) q' m v24 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v24 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  wb = pre ++ host ++ zbU :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In zbU host ->
  0 <= bp2 -> 1 <= p <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= fam < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j b, p <= j < z -> nth_error wb (Z.to_nat j) = Some b -> bv_unsigned b <> 0) ->
  evt asegs (postU XALL)
    (USTP 0x8dca4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 fam) x25 (Z_to_bv 64 (F + 32 + p)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP PZ Z255 BPZ FR WZ WNZ.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.

  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  destruct (wb_decomp wb p z ltac:(lia) WZ WNZ) as (pre2 & pstr & rest2 & EWB2 & LP2 & LS2 & NN2).
  pose proof (wb_strU m wb pre2 pstr rest2 WBB EWB2) as PSTR. rewrite LP2 in PSTR.
  assert (ETP : bv_unsigned tp - 164 = ERRNO_A) by (rewrite TPV; reflexivity).
  hideW MU WM.
  assert (EXIT : forall (e' : Z) y10 y11 y12 y13 yy14, p <= e' <= z ->
    evt asegs (postU XALL)
      (USTP 0x8dd10 q' x1 x5 x6 x7 y10 y11 y12 y13 yy14 x15 x16 x17 (Z_to_bv 64 F) (Z_to_bv 64 (F + 32 + e')) (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 fam) x25 (Z_to_bv 64 (F + 32 + p)) x28 x29 x30 x31 m)).
  { intros e' y10 y11 y12 y13 yy14 HE.
    assert (SHWW : shw m (F + 32) 256) by exact (shwW_now m SHF).
    assert (SHWp : shw m (F + 32 + p) (Z.of_nat (length pstr) + 1)) by (apply (shw_sub m (F + 32) 256 _ _ SHWW); lia).
    step. step. step.
    step.
    eapply evt_cut.
    { eapply (ic_strtol0 IC) with (S := F + 32 + p) (str := pstr) (errv := ev) (canary := canary) (lo := lo) (q := q').
      all: [> exact PSTR | rewrite ETP; exact ERRC | exact SSPG | exact SSPC | exact AE
      | exact (proj1 SHWp) | exact (proj1 (proj2 SHWp)) | exact (proj2 (proj2 SHWp)) | lia
      | exact ST | exact CLO | unfold A0_STRTOL_DEPTH; lia | lia
      | rewrite TPV; rewrite unsigned_lit by lia; lia | rewrite TPV; rewrite unsigned_lit by lia; lia
      | rewrite TPV; rewrite unsigned_lit by lia; reflexivity
      | lia | lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
    intros ms' PO. unfold strtol0_post_A in PO. rewrite ETP in PO.
    destruct PO as (y5 & y6 & y7 & z10 & z11 & z12 & z13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & ev' & -> & MUc & WMc & MI' & ST' & AE' & _ & _ & _ & ERRC').
    pose proof MUc as MUt. pose proof WMc as WMt.
    fs_sync FI RF MUc WMc FK LSUB.
    clear ST AE MI SHWW SHWp ERRC WBB.
    transport_after_call asegs m m' MUt WMt.
    absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) sub_fp_errno).
    clear MUt WMt.
    replace (ret_pc (Z_to_bv 64 580896)) with (Z_to_bv 64 580896) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    hideW MU WM.
    step. step. step.
    step. if_cases K1.
    { clear K1. unfold hid2 in MU, WM.
      apply (failU q' m' (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v24 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk); [mv_tacU| pv_tacU]. }
    clear K1.
    step. step.
    assert (SHWW : shw m' (F + 32) 256) by exact (shwW_now m' SHF).
    assert (SHWp : shw m' (F + 32 + p) (Z.of_nat (length pstr) + 1)) by (apply (shw_sub m' (F + 32) 256 _ _ SHWW); lia).
    eapply evt_cut.

    { eapply (ic_atoi IC) with (S := F + 32 + p) (str := pstr) (errv := ev') (canary := canary) (lo := lo) (q := q').
      all: [> exact PSTR | exact NN2 | rewrite ETP; exact ERRC' | exact SSPG | exact SSPC | exact AE'
      | exact (proj1 SHWp) | exact (proj1 (proj2 SHWp)) | exact (proj2 (proj2 SHWp)) | lia
      | exact ST' | exact CLO | unfold A0_RT_STACK; lia | lia
      | rewrite TPV; rewrite unsigned_lit by lia; lia | rewrite TPV; rewrite unsigned_lit by lia; lia
      | rewrite TPV; rewrite unsigned_lit by lia; reflexivity
      | lia | lia | exact MI' | reflexivity ]. }
    intros ms' PO. unfold strtol0_post_A in PO. rewrite ETP in PO.
    destruct PO as (t5 & t6 & t7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & ev2 & -> & MUc & WMc & MI2 & ST2 & AE2 & _ & _ & _ & ERRC2).
    pose proof MUc as MUt. pose proof WMc as WMt.
    fs_sync FI RF MUc WMc FK LSUB.
    clear ST' AE' MI' SHWW SHWp PSTR ERRC'.
    transport_after_call asegs m' m2 MUt WMt.
    absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) sub_fp_errno).
    clear MUt WMt.
    replace (ret_pc (Z_to_bv 64 580920)) with (Z_to_bv 64 580920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    hideW MU WM.
    pose proof (munch_refl [(q' + 24, q' + 32)]%Z m2) as MU0. pose proof (wmono_refl asegs m2) as WM0.
    step.
    step.
    step. step.
    step.   if_cases K2.
    2:{ clear K2. step.
      absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 24) (q' + 32) ltac:(lia) ltac:(lia)).
      env_sync AE2 MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (failU q' mm (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) w10 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk); [mv_tacU| pv_tacU] end. }
    clear K2.
    absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 24) (q' + 32) ltac:(lia) ltac:(lia)).
    env_sync AE2 MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    pose proof (bv_unsigned_in_range 64 w10) as PR. unfold bv_modulus in PR.
    rewrite <- (Z_to_bv_lit_self w10) in QC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (portfamU bp2 e' fam (bv_unsigned w10) srv pre host rest q' mm wb junk);
        [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| lia| lia| lia| lia| lia] end. }

  assert (LOOP : forall (k : nat) (c : Z) y13 y14, z - c < Z.of_nat k -> p <= c < z ->
    evt asegs (postU XALL)
      (USTP 0x8dcd8 q' x1 x5 x6 x7 (Z_to_bv 64 (F + 32 + c + 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 10) y13 y14 x15 x16 x17 (Z_to_bv 64 F) (Z_to_bv 64 (F + 32 + c)) (Z_to_bv 64 F) (Z_to_bv 64 srv) (Z_to_bv 64 fam) x25 (Z_to_bv 64 (F + 32 + p)) x28 x29 x30 x31 m)).
  { induction k as [|k IH]; intros c y13 y14 HK HCz; [lia|].
    destruct (wb_nthU wb (c + 1) LWB ltac:(lia)) as [b Hb]. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    pose proof (u8ro_read asegs m (F + 32) wb (c + 1) b (Z_to_bv 64 (F + 32 + c + 1)) WBB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    assert (HC255 : 0 <= c + 1 <= 255) by lia.
    step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
    step. step.
    replace (F + 32 + c + 1) with (F + 32 + (c + 1)) by lia.
    chkW 13 (c + 1) SHF HC255.
    step. lit_branch.
    step.
    replace (F + 32 + (c + 1)) with (F + 32 + c + 1) by lia.
    step. step. step.
    step. if_cases K0; zify_cond K0.
    - assert (BNZ : bv_unsigned b <> 0).
      { intros E0. rewrite E0 in K0. vm_compute in K0. discriminate K0. }
      assert (c + 1 <> z) by (intros E1; rewrite E1 in Hb; rewrite WZ in Hb; injection Hb as <-; apply BNZ; reflexivity).
      replace (Z_to_bv 64 (F + 32 + c + 2)) with (Z_to_bv 64 (F + 32 + (c + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (F + 32 + c + 1)) with (Z_to_bv 64 (F + 32 + (c + 1))) by (f_equal; lia).
      eapply (IH (c + 1)); lia.
    - step. replace (Z_to_bv 64 (F + 32 + c + 1)) with (Z_to_bv 64 (F + 32 + (c + 1))) by (f_equal; lia). eapply (EXIT (c + 1)); lia. }

  destruct (wb_nthU wb p LWB ltac:(lia)) as [b0 Hb0]. pose proof (bv_unsigned_in_range 8 b0) as BR0. unfold bv_modulus in BR0. cbn in BR0.
  pose proof (u8ro_read asegs m (F + 32) wb p b0 (Z_to_bv 64 (F + 32 + p)) WBB Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
  assert (HP255 : 0 <= p <= 255) by lia.
  step. step.
  chkW 10 p SHF HP255.
  step. lit_branch.
  step. step. step. step.
  step. if_cases K9; zify_cond K9.
  - eapply (EXIT p); lia.
  - assert (BNZ0 : bv_unsigned b0 <> 0).
    { intros E0. rewrite E0 in K9. vm_compute in K9. apply K9. reflexivity. }
    assert (p <> z) by (intros E1; rewrite E1 in Hb0; rewrite WZ in Hb0; injection Hb0 as <-; apply BNZ0; reflexivity).
    step. step. step. step.
    eapply (LOOP (S (Z.to_nat (z - p))) p); lia.
Qed.

#[using="U ulen ustr slack m0 RF0 OLB ULR"] Lemma sub_fp_F : forall a b, F <= a -> b <= F + 512 -> sub_fp [(a, b)] W0.
Proof.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & _).
  intros a b H1 H2 xo Ho. cbn [outside] in *. destruct Ho as (_ & H2' & _). split; [lia| exact I].
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v6brU : forall (bp2 z c a2v defport : Z) q' m wb junk
    x1 x6 x7 x10 x12 x13 x14 x16 x17 x21 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  0 <= bp2 -> 1 <= c < z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  a2v = (F + 32 + c) / 8 + 2147450880 ->
  evt asegs (postU XALL)
    (USTP 0x8dc5c q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 (Z_to_bv 64 (F + 32 + c + -1)) x12 x13 x14 (Z_to_bv 64 a2v) x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 (F + 33)) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP CZ Z255 BPZ DP WZ WNZ ->.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  destruct (wb_nthU wb c LWB ltac:(lia)) as [bc Hbc].
  assert (HC255 : 0 <= c <= 255) by lia.
  pose proof (munch_refl [(F + 32 + c, F + 32 + c + 1)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  destruct (cb_split1 m (F + 32) 256 wb (Z.to_nat c) bc WBC Hbc ltac:(lia)) as [TX1 TX23]. clear WBC.
  rewrite Z2Nat.id in TX23 by lia.
  remember (256 - Z.to_nat c - 1)%nat as nr eqn:Enr.
  step.
  step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-2) mod 18446744073709551616) with 18446744073709551614 in KU; lia).
  chkW 15 c SHF HC255.
  step. lit_branch.
  remember (F + 32 + c) as V eqn:EV.
  step; fix_lit_store.
  subst V.
  apply (rw_cells_reshape asegs _ _ _ [CB 1 [zbU]; CB nr (skipn (Z.to_nat c + 1) wb)]) in TX23;
    [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
  subst nr.
  pose proof (cb_join1 _ (F + 32) 256 wb (Z.to_nat c) zbU TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) LWB) as WBC.
  clear TX1 TX23.
  absorbW MU WM MU0 WM0 (sub_fp_F (F + 32 + c) (F + 32 + c + 1) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  hideW MU WM.

  assert (LW' : length (setb wb (Z.to_nat c) zbU) = 256%nat) by (rewrite setb_length; lia).
  assert (WZc : nth_error (setb wb (Z.to_nat c) zbU) (Z.to_nat c) = Some zbU) by (apply setb_same; lia).
  assert (WOTH : forall i, i <> Z.to_nat c -> nth_error (setb wb (Z.to_nat c) zbU) i = nth_error wb i) by (intros i Hi; apply setb_other; lia).
  set (wb' := setb wb (Z.to_nat c) zbU) in *. clearbody wb'.
  assert (WNZh : forall j' b, 1 <= j' < c -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  destruct (wb_decomp wb' 1 c ltac:(lia) WZc WNZh) as (pre & host & rest & EWB & LPRE & LHOST & NONUL).
  assert (WZ' : nth_error wb' (Z.to_nat z) = Some zbU) by (rewrite WOTH by lia; exact WZ).
  assert (WNZ' : forall j' b, c + 2 <= j' < z -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  destruct (wb_nthU wb' (c + 1) LW' ltac:(lia)) as [bn Hbn]. pose proof (bv_unsigned_in_range 8 bn) as BRn. unfold bv_modulus in BRn. cbn in BRn.
  assert (C2Z : bv_unsigned bn <> 0 -> c + 2 <= z).
  { intros Hn0. destruct (Z.eq_dec (c + 1) z) as [E|]; [|lia]. exfalso. rewrite E, WZ' in Hbn. injection Hbn as <-. apply Hn0. reflexivity. }
  clear WNZh WNZ WZ Hbc.
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  lazymatch type of WBB with bytes_at _ ?mm _ _ =>
    pose proof (u8ro_read asegs mm (F + 32) wb' (c + 1) bn (Z_to_bv 64 (F + 32 + c + 1)) WBB Hbn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  assert (HC1 : 0 <= c + 1 <= 255) by lia.
  step. step. step.
  chkW 12 (c + 1) SHF HC1.
  step. lit_branch.
  step.
  step.
  step.
  step.   if_cases K1; zify_cond K1.
  - clear K1 RD WBB. unfold hid2 in MU, WM.
    step.   step.
    replace (Z_to_bv 64 (F + 32 + c + 1)) with (Z_to_bv 64 (F + 32 + (c + 1))) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (portfamU bp2 (c + 1) 10 defport (F + 33) pre host rest q' mm wb' junk);
        [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia] end.
  - rewrite (unsigned_lit (bv_unsigned bn)) in K1 by lia.
    clear RD WBB. unfold hid2 in MU, WM.
    step.
    step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
    step.   step.
    replace (Z_to_bv 64 (F + 32 + c + 2)) with (Z_to_bv 64 (F + 32 + (c + 2))) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (portU bp2 (c + 2) z 10 (F + 33) pre host rest q' mm (Z_to_bv 64 defport) wb' junk);
        [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia| exact WZ'| exact WNZ'] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v6loopU : forall (k : nat) (bp2 z c a0v a1v a3v a2v defport : Z) q' m wb junk
    x1 x6 x7 x16 x17 x21 x24 x25 x26 x28 x29 x30 x31,
  z - c < Z.of_nat k ->
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  0 <= bp2 -> 1 <= c <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  a0v = F + 32 + c -> a1v = F + 32 + c + -1 -> a3v = c + -1 -> a2v = (F + 32 + c) / 8 + 2147450880 ->
  evt asegs (postU XALL)
    (USTP 0x8db1c q' x1 (Z_to_bv 64 (F + 32)) x6 x7 (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 (-1)) (Z_to_bv 64 a3v) (Z_to_bv 64 93) (Z_to_bv 64 a2v) x16 x17
          (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 (F + 33)) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until x31; intros HK INV PINV BP CZ Z255 BPZ DP WZ WNZ EA0 EA1 EA3 EA2; [lia|]. subst a0v a1v a3v.
  pose proof INV as INV'.
  destruct INV' as (_ & _ & _ & _ & WBC & _ & _ & _ & _ & SHF & _).
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  clear WBC.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (wb_nthU wb c LWB ltac:(lia)) as [bc Hbc]. pose proof (bv_unsigned_in_range 8 bc) as BR. unfold bv_modulus in BR. cbn in BR.
  pose proof (u8ro_read asegs m (F + 32) wb c bc (Z_to_bv 64 (F + 32 + c)) WBB Hbc ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step.
  step.   if_cases K0; zify_cond K0.
  { clear K0. apply (failU q' m (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk); assumption. }
  rewrite (unsigned_lit (bv_unsigned bc)) in K0 by lia.
  assert (CLT : c < z). { destruct (Z.eq_dec c z) as [E|]; [|lia]. exfalso. subst c. rewrite WZ in Hbc. injection Hbc as <-. apply K0. reflexivity. }
  step.   if_cases K1; zify_cond K1.
  { clear K1. apply (v6brU bp2 z c a2v defport q' m wb junk); try assumption; lia. }
  clear K1.
  step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
  step. step. step.
  step. step.
  assert (HC1 : 0 <= c + 1 <= 255) by lia.
  replace (F + 32 + c + 1) with (F + 32 + (c + 1)) by lia.
  chkW 15 (c + 1) SHF HC1.
  step.
  lit_branch.
  eapply (IH bp2 z (c + 1) _ _ _ _ defport q' m wb junk); try eassumption; try lia.
  rewrite unsigned_lit by lia. rewrite shiftr3_div. reflexivity.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v6U : forall (bp2 z defport : Z) q' m wb junk
    x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  0 <= bp2 -> 1 <= z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  evt asegs (postU XALL)
    (USTP 0x8daf0 q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP Z255 BPZ DP WZ WNZ.
  pose proof INV as INV'.
  destruct INV' as (_ & _ & _ & _ & WBC & _ & _ & _ & _ & SHF & _).
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  step.
  step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
  step. step. step. step.
  step. step. step.
  assert (HC1 : 0 <= 1 <= 255) by lia.
  chkW 15 1 SHF HC1.
  step. lit_branch.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (v6loopU (S (Z.to_nat z)) bp2 z 1 _ _ _ _ defport q' mm wb junk); [lia| exact INV| exact PINV| lia| lia| lia| lia| lia| exact WZ| exact WNZ| | | |] end.
  - lia.
  - lia.
  - lia.
  - rewrite unsigned_lit by lia. rewrite shiftr3_div. f_equal. f_equal. lia.
Qed.

End W.
