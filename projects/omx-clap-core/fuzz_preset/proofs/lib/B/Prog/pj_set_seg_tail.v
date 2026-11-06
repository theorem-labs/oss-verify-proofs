(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment TAIL of pj_set's image-B walk (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of
   lib/B/Prog/pj_set_defs.v): the shared tail BOTH arms join at, from PJS_TAIL (+0x50) to the epilogue PJS_EPI.
     +0x50  mv a1, s0                 a1 := val
     +0x54  jal __asan_memcpy         (dest, val, 56): YGcallMxmn.v aj_intrin_at_xm_fr at OCpy
     +0x58  li a2, 56
     +0x5c  mv a0, s0                 a0 := val
     +0x60  mv a1, zero
     +0x64  jal __asan_memset         (val, 0, 56): aj_intrin_at_xm_fr at OSet
     +0x68  li a0, 0
     +0x6c  j +0x88                   into the epilogue (pjs_seg_epi, a premise)
   proves no function (kind: segment lemma). The seven instructions are stepped concretely (YA0n.v SRr_step with
   YK14.v step_addi_at / step_jal_link; the words are read from the image table PI_prog_B, certified by the
   listing, and decoded by computation), so the memory moves only at the two intrinsic calls. The cut is after
   pj_set's frees, so its journal is at the re-hiding relation WLE' (YA0nH.wle' over preset's zone): the stretch is
   stepped plainly under YGcfRhLift.ra_rh_of_SRr, and the two calls are YGcallMxmn.v's R rule aj_intrin_at_xm_frR at
   WLE' (an intrinsic keeps the world, so the journal's world conjunct passes through). The calls are m-form rules
   (the texts are YGcallMxmn.v aintrin_realizes_xm), so the memnorm keep of pjs_invR crosses both: the
   epilogue's pjs_invR takes the cut's keep, then memcpy's, then memset's. The cut's own obligation (pjs_TAIL's last
   clause) turns the two writes into the post at the cut's ly / S / Hp / W (the intrinsics keep all four).
   Numerals: 48 / 56 (LENGTH: the frame and the struct pj); 4 / 8 / 12 / 16 / 20 / 24 / 28 / 56 / 88 (DERIVED: pc
   offsets from the cut); register numbers 0, 1, 2, 3, 4, 8, 10, 11, 12 (WORD). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_set_defs pj_set_steps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfRhLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section tl. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation WLE' := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WLE'_refl := (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WLE'_trans := (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* ---- the segment ---- *)
Theorem pjs_seg_tail_holds : forall CTX0 dd,
  pjs_texts B ARx CTX0 dd -> pjs_seg_epi B ARx CTX0 dd -> pjs_seg_tail B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT HEPI en ly S Hp W regs mem md k HPRE HCUT.
destruct TXT as (_ & _ & _ & _ & AMCPY & AMSET).
pose proof HPRE as HPRE0.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold pjs_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & HFWIN & _).
pose proof HFPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0) & HROD0 & HSTKHI0).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HCUT as (HINV & HROOM & dest & Lam2 & peak2 & cnt2 & fail2 & ran2 & c & ok & Ha0 & Ha2 & HLED & Ecnt &
  Hoks & Hfa & HNODEW & HSLOTW & HSLOTD & HDISJ & HDCEIL & HWCEIL & HWR & HSRC & HNIMG & HFINAL).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD & HMN).
pose proof HSLOTW as (Hw4096 & _ & Hwrw & Hwamr & Hwown & Hwra & Hwhull).
pose proof HSLOTD as (Hd4096 & _ & Hdrw & Hdamr & Hdown & Hdra & Hdhull).
assert (HSTKE : ESTACK + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity).
  assert (HE : STK_RT_ECALL = ESTACK) by reflexivity. lia. }
assert (Hes : ESTACK = 4096) by reflexivity.
(* the two write ranges avoid pj_set's own stack window, so they avoid each call's ESTACK window below sp1 *)
assert (HNOSTK : forall a, (dest <= a < dest + 56) \/ (js_w en <= a < js_w en + 56) ->
  ~ (js_sp0 en + js_d en + (- 48 - js_d en) - ESTACK <= a < js_sp0 en + js_d en + (- 48 - js_d en))).
{ intros a Ha Hc. unfold js_sp0 in Hc.
  destruct Ha as [Ha | Ha]; [destruct (Hdown a Ha) as (_ & Hn) | destruct (Hwown a Ha) as (_ & Hn)];
  apply Hn; lia. }
assert (HNOSTK1 : forall a, (dest <= a < dest + 56) \/ (js_w en <= a < js_w en + 56) ->
  ~ (js_sp1 en - ESTACK <= a < js_sp1 en)).
{ intros a Ha Hc. apply (HNOSTK a Ha). unfold js_sp1, js_sp0, PJS_FR in Hc. unfold js_sp0. lia. }
(* both 56-byte ranges lie below pj_set's frame (the allocator ceiling is below the stack) *)
assert (HDLOW : dest + 56 <= js_sp1 en) by (unfold js_sp1, js_sp0, PJS_FR; lia).
assert (HWLOW : js_w en + 56 <= js_sp1 en) by (unfold js_sp1, js_sp0, PJS_FR; lia).
assert (HSPLO : YM05.alloc_ceiling <= js_sp1 en - ESTACK) by (unfold js_sp1, js_sp0, PJS_FR; lia).
(* the stack lies above the allocator ceiling, so no shadow cell is in a call's ESTACK window *)
assert (HSHSTK : forall s, kLowMemEnd <= s < kHighShadowEnd ->
  ~ (js_sp0 en + js_d en + (- 48 - js_d en) - ESTACK <= s < js_sp0 en + js_d en + (- 48 - js_d en))).
{ intros s Hs Hc. unfold js_sp0 in Hc. lia. }
assert (HWTOP : js_w en + 56 <= 2 ^ 63) by (destruct Hwamr as [Hx | (Hx1 & Hx2)]; lia).
assert (HWHI : js_w en + 56 <= kHighMemEnd - 1) by (destruct Hwamr as [Hx | (Hx1 & Hx2)]; lia).
assert (HDHI : dest + 56 <= kHighMemEnd - 1) by (destruct Hdamr as [Hx | (Hx1 & Hx2)]; lia).
assert (HDAPP : dest + 56 <= kLowMemEnd - 1 \/ kHighMemBeg <= dest)
  by (destruct Hdamr as [Hx | (Hx1 & Hx2)]; [left | right]; lia).
(* the same, at any register state whose sp is pj_set's (the call's argument registers) *)
assert (HSPT : forall rr : bvmap 5 word, spZ rr = spZ regs ->
  forall a, (dest <= a < dest + 56) \/ (js_w en <= a < js_w en + 56) -> ~ (spZ rr - ESTACK <= a < spZ rr)).
{ intros rr Err a Ha. rewrite Err, Hsp. exact (HNOSTK1 a Ha). }
unfold pjs_cfg.
(* the plain stretch, under ra_rh_of_SRr (the cut is at WLE' already) *)
apply YGcfRhLift.ra_rh_of_SRr.
(* ======== +0x50  mv a1, s0 ======== *)
pjs_fd PJS_TAIL Hl1 Hd1.
eapply (pjs_step_addi W regs mem md _ PJS_TAIL _ _ _ _ (11%bv : bv 5) (getr regs (8%bv : bv 5)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
replace (v_addi (Z_to_bv 64 (BASE + PJS_TAIL)) 4) with (Z_to_bv 64 (BASE + (PJS_TAIL + 4)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x54  jal __asan_memcpy ======== *)
pjs_fd (PJS_TAIL + 4) Hl2 Hd2.
eapply (pjs_step_jal W _ mem _ _ (PJS_TAIL + 4) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJS_TAIL + 8)))
  (Z_to_bv 64 (@pa_sigma _ B_prog_listing PA AS___asan_memcpy)) Hl2 Hd2).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rT _ ?mT _) ?mdT) _ =>
  eapply (YGcallMxmn.aj_intrin_at_xm_frR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' WLE'_refl WLE'_trans OCpy
    (@pa_sigma _ B_prog_listing PA AS___asan_memcpy) AMCPY W rT mT
    (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp mdT k
    dest (js_w en) 56 (- 48 - js_d en) (Z_to_bv 64 (BASE + (PJS_TAIL + 8))) HJ2) end.
  - pjs_regval. exact Ha0.
  - pjs_regval. exact H8.
  - pjs_regval. exact Ha2.
  - lia.
  - lia.
  - lia.
  - unfold spZ. pjs_regval. change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite Hsp.
    unfold js_sp1, js_sp0, PJS_FR. lia.
  - lia.
  - lia.
  - lia.
  - pjs_regval. rewrite (HKEPT 3%bv) by (unfold PJS_KEPT; left; reflexivity). exact Hgp0.
  - pjs_regval. rewrite (HKEPT 4%bv) by (unfold PJS_KEPT; right; left; reflexivity). exact Htp0.
  - pjs_regval. reflexivity.
  - apply (YC1fP.ret_ok_codeptr_v (PI := PA));
      [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity].
  - intros a Ha. split; [exact (HWR a (or_introl Ha)) | exact (HNOSTK a (or_introl Ha))].
  - exact Hdamr.
  - exact Hdra.
  - intros _. exact Hdhull.
  - split; [lia|]. split; [lia|].
    split; [intros a Ha; split; [exact (HSRC a Ha)|];
            eapply HSPT; [unfold spZ; pjs_regval; reflexivity | right; exact Ha]|].
    split; [destruct (Z_le_gt_dec (dest + 56) (js_w en)) as [H|H]; [left; lia|];
            right; destruct (Z_le_gt_dec (js_w en + 56) dest) as [H2|H2]; [lia|];
            exfalso; exact (HDISJ (Z.max dest (js_w en)) ltac:(lia) ltac:(lia))|].
    split; [exact Hwamr|]. split; [exact Hwra | intros _; exact Hwhull]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Hcpy & Hfr3 & Hpres3 & Hmn3).
assert (K3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> r <> (1%bv : bv 5) -> r <> (11%bv : bv 5) ->
  getr regs3 r = getr regs r).
{ intros r Hcs H1 H11. rewrite (pjs_pres _ _ r HP3 Hcs), !getr_other by assumption. reflexivity. }
assert (K3sp : spZ regs3 = spZ regs).
{ rewrite (pjs_pres_sp _ _ HP3). unfold spZ. rewrite !getr_other by pjs_regne. reflexivity. }
(* ======== +0x58 .. +0x60: a2 := 56, a0 := s0, a1 := 0 ======== *)
pjs_fd (PJS_TAIL + 8) Hl3 Hd3.
eapply (pjs_step_addi W regs3 mem3 md3 _ (PJS_TAIL + 8) _ _ _ _ (12%bv : bv 5) (w64 56) Hl3 Hd3).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X3.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJ3) as HJ4.
replace (v_addi (Z_to_bv 64 (BASE + (PJS_TAIL + 8))) 4) with (Z_to_bv 64 (BASE + (PJS_TAIL + 12)))
  by (apply bv_eq; vm_compute; reflexivity).
assert (HS0c : getr regs3 (8%bv : bv 5) = w64 (js_w en)).
{ rewrite <- H8. apply K3; [pjs_cs | pjs_regne | pjs_regne]. }
pjs_fd (PJS_TAIL + 12) Hl4 Hd4.
eapply (pjs_step_addi W _ mem3 _ _ (PJS_TAIL + 12) _ _ _ _ (10%bv : bv 5) (getr regs3 (8%bv : bv 5)) Hl4 Hd4).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  rewrite getr_other by pjs_regne. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X4.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJ4) as HJ5.
replace (v_addi (Z_to_bv 64 (BASE + (PJS_TAIL + 12))) 4) with (Z_to_bv 64 (BASE + (PJS_TAIL + 16)))
  by (apply bv_eq; vm_compute; reflexivity).
pjs_fd (PJS_TAIL + 16) Hl5 Hd5.
eapply (pjs_step_addi W _ mem3 _ _ (PJS_TAIL + 16) _ _ _ _ (11%bv : bv 5) (w64 0) Hl5 Hd5).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  rewrite getr_zero. unfold v_addi, w64. rewrite Z.add_0_r. reflexivity. }
intros X5.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5 HJ5) as HJ6.
replace (v_addi (Z_to_bv 64 (BASE + (PJS_TAIL + 16))) 4) with (Z_to_bv 64 (BASE + (PJS_TAIL + 20)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x64  jal __asan_memset ======== *)
pjs_fd (PJS_TAIL + 20) Hl6 Hd6.
eapply (pjs_step_jal W _ mem3 _ _ (PJS_TAIL + 20) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJS_TAIL + 24)))
  (Z_to_bv 64 (@pa_sigma _ B_prog_listing PA AS___asan_memset)) Hl6 Hd6).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X6.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6 HJ6) as HJ7.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rT _ ?mT _) ?mdT) _ =>
  eapply (YGcallMxmn.aj_intrin_at_xm_frR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' WLE'_refl WLE'_trans OSet
    (@pa_sigma _ B_prog_listing PA AS___asan_memset) AMSET W rT mT
    (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp mdT k
    (js_w en) 0 56 (- 48 - js_d en) (Z_to_bv 64 (BASE + (PJS_TAIL + 24))) HJ7) end.
  - pjs_regval. exact HS0c.
  - pjs_regval. reflexivity.
  - pjs_regval. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. pjs_regval. change (bv_unsigned (getr regs3 2)) with (spZ regs3).
    rewrite K3sp, Hsp. unfold js_sp1, js_sp0, PJS_FR. lia.
  - lia.
  - lia.
  - lia.
  - pjs_regval. rewrite (K3 (3%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne)).
    rewrite (HKEPT 3%bv) by (unfold PJS_KEPT; left; reflexivity). exact Hgp0.
  - pjs_regval. rewrite (K3 (4%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne)).
    rewrite (HKEPT 4%bv) by (unfold PJS_KEPT; right; left; reflexivity). exact Htp0.
  - pjs_regval. reflexivity.
  - apply (YC1fP.ret_ok_codeptr_v (PI := PA));
      [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity].
  - intros a Ha. split; [|exact (HNOSTK a (or_intror Ha))].
    destruct (HWR a (or_intror Ha)) as [Hw | Hw]; [left | right; exact Hw].
    eapply awr_byte_mono; [exact Hw|]. intros b n Hin Hb.
    exact Hin.
  - exact Hwamr.
  - eapply range_addressable_agree; [|exact Hwra].
    intros x Hx. pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx.
    unfold shadow_of_addr. apply Hfr3; [lia | | apply HSHSTK; lia].
    destruct HDAPP as [Hz | Hz]; lia.
  - intros _ s Hs.
    pose proof (pjs_hull_bounds (js_w en) 56 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hsb.
    rewrite Hfr3; [exact (Hwhull s Hs) | lia | destruct HDAPP as [Hz | Hz]; lia | apply HSHSTK; lia].
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ8 & HP4 & Ha04 & Hset & Hfr4 & Hpres4 & Hmn4).
assert (K4 : forall r : bv 5, acallee_saved (bv_unsigned r) -> r <> (1%bv : bv 5) -> r <> (10%bv : bv 5) ->
  r <> (11%bv : bv 5) -> r <> (12%bv : bv 5) -> getr regs4 r = getr regs3 r).
{ intros r Hcs H1 H10 H11 H12. rewrite (pjs_pres _ _ r HP4 Hcs), !getr_other by assumption. reflexivity. }
assert (K4sp : spZ regs4 = spZ regs3).
{ rewrite (pjs_pres_sp _ _ HP4). unfold spZ. rewrite !getr_other by pjs_regne. reflexivity. }
(* ======== +0x68  li a0, 0 ; +0x6c  j +0x88 ======== *)
pjs_fd (PJS_TAIL + 24) Hl7 Hd7.
eapply (pjs_step_addi W regs4 mem4 md4 _ (PJS_TAIL + 24) _ _ _ _ (10%bv : bv 5) (w64 0) Hl7 Hd7).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  rewrite getr_zero. unfold v_addi, w64. rewrite Z.add_0_r. reflexivity. }
intros X7.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7 HJ8) as HJ9.
replace (v_addi (Z_to_bv 64 (BASE + (PJS_TAIL + 24))) 4) with (Z_to_bv 64 (BASE + (PJS_TAIL + 28)))
  by (apply bv_eq; vm_compute; reflexivity).
pjs_fd (PJS_TAIL + 28) Hl8 Hd8.
eapply (pjs_step_j W _ mem4 _ _ (PJS_TAIL + 28) _ _ _ (Z_to_bv 64 (BASE + PJS_EPI)) Hl8 Hd8).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X8.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X8 HJ9) as HJA.
(* ======== the epilogue (an SRr' segment: the plain stretch ends here) ======== *)
apply SRr_ret.
apply (HEPI en ly S Hp W _ mem4 _ k HPRE0).
split.
{ (* the invariant at the epilogue: the two writes left the frame and the window alone *)
  assert (KEEP : forall a, ~ (dest <= a < dest + 56) -> ~ (js_w en <= a < js_w en + 56) ->
    ~ (js_sp1 en - ESTACK <= a < js_sp1 en) -> 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
  { intros a Hd' Hw' Hs' Ha. rewrite Hfr4; [|lia | exact Hw' |].
    - rewrite Hfr3; [reflexivity | lia | exact Hd' |].
      unfold js_sp1, js_sp0, PJS_FR in Hs'. unfold js_sp0. lia.
    - unfold js_sp1, js_sp0, PJS_FR in Hs'. unfold js_sp0. lia. }
  assert (KFR : forall a, js_sp1 en <= a < js_sp0 en + js_d en ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
  { intros a Ha. apply KEEP; [| | unfold js_sp1, js_sp0, PJS_FR in *; lia |
      unfold js_sp1, js_sp0, PJS_FR in *; lia].
    - intros Hx. lia.
    - intros Hx. lia. }
  assert (KV : forall p n v, val_mem SEGS (mrestrict (w_H W) mem) p n v -> js_sp1 en <= p ->
    p + Z.of_nat n <= js_sp0 en -> val_mem SEGS (mrestrict (w_H W) mem4) p n v).
  { intros p n v Hv Hlo Hhi kk Hk.
    rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem4 _ (KFR (p + Z.of_nat kk) ltac:(lia))). exact (Hv kk Hk). }
  split; [exact HJA|].
  split; [intros a Ha Hfp; rewrite (KFR a ltac:(unfold js_sp1, PJS_FR; lia)); exact (HWIN a Ha Hfp)|].
  split.
  { unfold spZ. pjs_regval. change (bv_unsigned (getr regs4 2)) with (spZ regs4).
    rewrite K4sp, K3sp. exact Hsp. }
  split; [exact (KV _ 8%nat _ Hra ltac:(unfold js_sp1, js_sp0, PJS_FR; lia) ltac:(cbn [Z.of_nat]; unfold js_sp1, js_sp0, PJS_FR; lia))|].
  split; [exact (KV _ 8%nat _ Hs0 ltac:(unfold js_sp1, js_sp0, PJS_FR; lia) ltac:(cbn [Z.of_nat]; unfold js_sp1, js_sp0, PJS_FR; lia))|].
  split; [exact (KV _ 8%nat _ Hs1 ltac:(unfold js_sp1, js_sp0, PJS_FR; lia) ltac:(cbn [Z.of_nat]; unfold js_sp1, js_sp0, PJS_FR; lia))|].
  split; [exact (KV _ 8%nat _ Hs2 ltac:(unfold js_sp1, js_sp0, PJS_FR; lia) ltac:(cbn [Z.of_nat]; unfold js_sp1, js_sp0, PJS_FR; lia))|].
  split; [exact (KV _ 8%nat _ Hs3 ltac:(unfold js_sp1, js_sp0, PJS_FR; lia) ltac:(cbn [Z.of_nat]; unfold js_sp1, js_sp0, PJS_FR; lia))|].
  split; [exact (KV _ 8%nat _ Hs4 ltac:(unfold js_sp1, js_sp0, PJS_FR; lia) ltac:(cbn [Z.of_nat]; unfold js_sp1, js_sp0, PJS_FR; lia))|].
  split.
  { rewrite getr_other by pjs_regne. rewrite (K4 (8%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne) ltac:(pjs_regne) ltac:(pjs_regne)). exact HS0c. }
  split.
  { rewrite getr_other by pjs_regne. rewrite (K4 (18%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne) ltac:(pjs_regne) ltac:(pjs_regne)),
      (K3 (18%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne)). exact H18. }
  split.
  { rewrite getr_other by pjs_regne. rewrite (K4 (20%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne) ltac:(pjs_regne) ltac:(pjs_regne)),
      (K3 (20%bv : bv 5) ltac:(pjs_cs) ltac:(pjs_regne) ltac:(pjs_regne)). exact H20. }
  split.
  { intros r Hr.
    assert (Hcs : acallee_saved (bv_unsigned r)).
    { unfold PJS_KEPT in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pjs_cs |]). destruct Hr. }
    rewrite getr_other by pjs_kept_ne.
    rewrite (K4 r Hcs ltac:(pjs_kept_ne) ltac:(pjs_kept_ne) ltac:(pjs_kept_ne) ltac:(pjs_kept_ne)),
      (K3 r Hcs ltac:(pjs_kept_ne) ltac:(pjs_kept_ne)). exact (HKEPT r Hr). }
  split.
  { intros a Ha. apply Hpres4, Hpres3. exact (HPRES a Ha). }
  split.
  { intros a Hro Hos Her.
    rewrite KEEP; [exact (HROD a Hro Hos Her) | | | |].
    - intros Hx. assert (Hi : in_img SEGS a).
      { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
      exact (HNIMG a (or_introl Hx) Hi).
    - intros Hx. assert (Hi : in_img SEGS a).
      { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
      exact (HNIMG a (or_intror Hx) Hi).
    - assert (Hi : in_img SEGS a).
      { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
      pose proof (Hsegs a Hi). lia.
    - assert (Hi : in_img SEGS a).
      { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
      pose proof (Hsegs a Hi). lia. }
  (* the memnorm keep: the cut's, then each intrinsic's (YGcallMxmn.v aintrin_realizes_xm's last conjunct) *)
  intros Hmn0. exact (Hmn4 (Hmn3 (HMN Hmn0))). }
(* The post, from the cut's own obligation *)
apply (HFINAL mem4 _ _).
- intros i Hi. rewrite Hfr4; [| lia | | ].
  + rewrite (Hcpy i Hi). reflexivity.
  + intros Hx. exact (HDISJ (dest + i) ltac:(lia) ltac:(lia)).
  + apply (HNOSTK (dest + i)). left. lia.
- intros i Hi. rewrite (Hset i Hi). cbn [Z.modulo]. reflexivity.
- intros a Ha Hd' Hw' Hs'. rewrite Hfr4; [| lia | exact Hw' |].
  + rewrite Hfr3; [reflexivity | lia | exact Hd' |].
    unfold js_sp1, js_sp0, PJS_FR in Hs'. unfold js_sp0. lia.
  + unfold js_sp1, js_sp0, PJS_FR in Hs'. unfold js_sp0. lia.
- intros a Ha. apply Hpres4, Hpres3. exact Ha.
- rewrite getr_same by pjs_regne. reflexivity.
Qed.

End tl.
