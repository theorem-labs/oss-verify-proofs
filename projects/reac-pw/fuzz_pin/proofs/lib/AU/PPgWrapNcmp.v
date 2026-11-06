(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_ubjson_encoder/lib/S8/AsanAcct.v, with its module paths and module names changed; 403 of its 523 lines of code are new or changed and 1138 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FMbz_clean.v, with its module paths and module names changed; 344 of its 386 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/A/HPgWrapNcmp.v's hd_strncmp_core (itself reac-pw/fuzz_pin's
   lib/A/PPgWrapNcmp.v pin_strncmp_core at 90722657971) re-run with the caller's frame hole of lib/A/HPgHole.v
   (ecall_preH in, the hole post out), as lib/A/Rt/FMrt_lift.v rt_post_roU_win re-runs rt_post_ro_win with
   lib/A/Rt/FMupoison.v ARU_frame: hd_rt_post_roH_win is rt_post_roU_win with HPgHole.ARH_frame in place of
   ARU_frame; the walk's premises that AR gives (the stack window, the runtime cells, the read-only views) are read
   off AR of the unpoisoned memory and carried to the memory itself, which agrees with it off the hole; the rest
   is pin's proof. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgWrapNcmpH.v, with its module paths and module names changed; 126 of its 278 lines of code are new or changed and 234 lines of the source are left out. *)
(* reac-pw/fuzz_pin, image A (fuzz_pin.asan 3e4859aed23f): lib/A/PPgWrap.v `astrncmp_realizes` at the strncmp
   trampoline __interceptor_trampoline_strncmp 0x41914 (`j 0x42400`), the wrapper ___interceptor_strncmp 0x42400.
   rule 24 (reuse): PORT. The body walk is libreac/fuzz_boxreg's released one (lib/A/Bz/A/I_strncmp.v istrncmp_spec
   with I_strncmpw / w2 / w3, relocated to pin in lib/A/Bz), read at the call site through boxreg's released adapter
   (lib/A/Rt/FMstrncmp.v astrncmp_holds and the FM* files under it, relocated to pin in lib/A/Rt). This file is the
   adapter from that walk to pin's text: the proof is FMstrncmp.v's astrncmp_holds with its premises taken from
   PPgWrap's (awrap_str, amem_range over each string and 7 more bytes, aro_unowned) instead of fm's (cstr_ok,
   rom_viewN, rom_viewO), and with its answer read as PPgWrap's (the result word is 0 exactly when
   lib/Spec/StrFun.v strncmp_model is 0).
   - stack: PPgWrap gives ecall_pre, the 2 * ESTACK window below sp and its presence; the layout law
     (YG0f.v lo_stk_ceil) gives alloc_ceiling <= ly_stk_lo, which makes it fm's ecall_pre_k.
   - strings: each string's bytes and NUL (garr8), its shadow (range_addressable, shadow_hull_vis) and
     amem_range over len + 8 give the walk's bytes_at and its range check chk_ok (FMrt_pre.v chk_ok_of_pre);
     a string lies outside [sp - 2 * ESTACK, sp), so it lies wholly below sp - 2 * ESTACK or at or above sp,
     which is the walk's separation premise (sep_of_win).
   - read-only bytes: aro_unowned IS fm's rom_viewN; fm's rom_viewO (the runtime-owned read-only bytes read as
     the image's) comes from AR's constant cells (StrncmpView.v fm_rom_viewO_of_AR) under ro_owned_pinned, a
     fact about the symbol record B and the image alone: pin_astrncmp_A takes it as the premise ROP, and
     pin_astrncmp discharges it for every TfibSyms record by lib/A/Rt/PinRoPins.v (a check over pin's own
     lib/A/AF0m.v tables and image); AR_laws holds of every record (lib/Reusable/YG0q.v AR_laws_ok).
   - answer: the walk returns strncmp_res (Bz/A/IcptSpec.v), which is 0 exactly when the first n bytes of the two
     strings with their NULs agree (FMstrncmp.v strncmp_strs); strncmp_model is 0 exactly then too
     (model_zero).
   The top lemmas: pin_astrncmp (every B with TfibSyms B) and pin_astrncmp_TfibB (pin's record, lib/A/AD2l.v). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgWrapNcmp.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): module paths lib.A -> lib.AU (the core files A<xyz> -> Y<xyz>); lib.A.PPgWrap, image-independent, kept; no numeral changed (every address numeral checked on the asan-ubsan image); by hand, comments only: the program's call of the trampoline is reac_box_pin_parse 0x80da0 in this image (the function's code differs between the two images, so that address is read from this image's code, not moved by offset), and two comments name lib/AU/Rt/PinRoPins.v and lib/AU/YD2l.v. The comment lines above describe how lib/A/PPgWrapNcmp.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import FMrt_lift FMrt_pre FMbz_clean.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import StrncmpFmh.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require StrncmpDef StrncmpView FMstrncmp WrapRo PinRoPins.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgWrap.
Require OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.IcptSpec.
Require OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.I_strncmp.
Require OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.I_tramp.
Require OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.R_isPoisoned.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SCS := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.IcptSpec.
Module SCP := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.I_strncmpw3.
Module SCW := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.I_strncmp.
Module TRP := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.R_isPoisoned.
Module SF := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec.StrFun.
Module FMS := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt.FMstrncmp.
Module SV := OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt.StrncmpView.

(* The entry the program code calls (`jal 0x41914` at reac_box_pin_parse 0x80da0): boxreg's STRNCMP_ENTRY,
   relocated. *)
Lemma PC_strncmp_pin : StrncmpDef.STRNCMP_ENTRY = 0x41914.
Proof. reflexivity. Qed.

(* ---- the answer: strncmp_model is 0 exactly when the compared prefixes agree ---- *)
Definition u8s (l : list byte) : list Z := map (fun b : byte => bv_unsigned b) l.

Lemma u8_nz : forall (l : list byte) b, ~ In (Z_to_bv 8 0) l -> In b l -> bv_unsigned b <> 0.
Proof.
  intros l b Hn Hb E. apply Hn.
  replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma walk_zero : forall (ls rs : list byte) (k : nat) (d : Z),
  ~ In (Z_to_bv 8 0) ls -> ~ In (Z_to_bv 8 0) rs ->
  SF.strncmp_walk (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) k = Some d ->
  (d = 0 <-> firstn (S k) (u8s ls ++ [0]) = firstn (S k) (u8s rs ++ [0])).
Proof.
  induction ls as [|a ls IH]; intros rs k d N1 N2 HW.
  - destruct rs as [|b rs].
    + cbn in HW. injection HW as <-. split; intros _; reflexivity.
    + cbn [app SF.strncmp_walk] in HW.
      change (bv_unsigned (Z_to_bv 8 0)) with 0 in HW. cbn [Z.eqb orb] in HW. injection HW as <-.
      assert (Hb : bv_unsigned b <> 0) by (apply (u8_nz (b :: rs)); [exact N2 | left; reflexivity]).
      unfold u8s. cbn [map app firstn]. split; intros H; [lia | injection H as H; lia].
  - assert (Ha : bv_unsigned a <> 0) by (apply (u8_nz (a :: ls)); [exact N1 | left; reflexivity]).
    destruct rs as [|b rs].
    + cbn [app SF.strncmp_walk] in HW.
      change (bv_unsigned (Z_to_bv 8 0)) with 0 in HW.
      rewrite (proj2 (Z.eqb_neq _ _) Ha) in HW. cbn [Z.eqb orb] in HW. injection HW as <-.
      unfold u8s. cbn [map app firstn]. split; intros H; [lia | injection H as H; lia].
    + assert (Hb : bv_unsigned b <> 0) by (apply (u8_nz (b :: rs)); [exact N2 | left; reflexivity]).
      assert (N1' : ~ In (Z_to_bv 8 0) ls) by (intros H; apply N1; right; exact H).
      assert (N2' : ~ In (Z_to_bv 8 0) rs) by (intros H; apply N2; right; exact H).
      cbn [app SF.strncmp_walk] in HW.
      rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hb) in HW. cbn [orb] in HW.
      unfold u8s. cbn [map app firstn]. fold (u8s ls) (u8s rs).
      destruct (Nat.eqb_spec k 0) as [K0|K0].
      * subst k. cbn [orb] in HW. injection HW as <-. cbn [firstn].
        split; intros H; [f_equal; lia | injection H as H; lia].
      * cbn [orb] in HW.
        destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
        -- cbn [negb] in HW. destruct k as [|k']; [lia|].
           rewrite (IH rs k' d N1' N2' HW). rewrite Eab.
           split; intros H; [rewrite H; reflexivity | injection H as H; exact H].
        -- cbn [negb] in HW. injection HW as <-.
           split; intros H; [lia | injection H as H _; lia].
Qed.

Lemma model_zero : forall (ls rs : list byte) (n d : Z), 0 <= n ->
  ~ In (Z_to_bv 8 0) ls -> ~ In (Z_to_bv 8 0) rs ->
  SF.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
  (d = 0 <-> StrncmpDef.fm_strn_eq (Z.to_nat n) (u8s ls) (u8s rs)).
Proof.
  intros ls rs n d Hn N1 N2 HM. unfold SF.strncmp_model in HM. unfold StrncmpDef.fm_strn_eq.
  destruct (Z.eqb_spec n 0) as [->|NZ].
  - injection HM as <-. cbn. split; intros _; reflexivity.
  - replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
    exact (walk_zero ls rs (Z.to_nat (n - 1)) d N1 N2 HM).
Qed.

(* ---- the strings ---- *)
Lemma map_bv_u8s : forall l : list byte, map (Z_to_bv 8) (u8s l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [u8s map]. fold (u8s l). rewrite IH. f_equal.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma u8s_ok : forall l : list byte, ~ In (Z_to_bv 8 0) l -> Forall (fun c => c <> 0) (u8s l).
Proof.
  intros l Hn. apply Forall_forall. intros c Hc. unfold u8s in Hc. apply in_map_iff in Hc as (b & <- & Hb).
  exact (u8_nz l b Hn Hb).
Qed.

(* a string outside the callee's window lies wholly below it or wholly at or above sp *)
Lemma sep_of_win : forall x len sp E sz, 0 <= len -> sz <= len + 1 -> 2256 <= E ->
  (forall a, x <= a <= x + len -> ~ (sp - E <= a < sp)) ->
  x + sz <= sp - 2256 \/ sp <= x.
Proof.
  intros x len sp E sz Hl Hs HE H.
  destruct (Z_lt_le_dec (x + len) (sp - E)) as [L|L]; [left; lia|]. right.
  destruct (Z_lt_le_dec x (sp - E)) as [L2|L2]; [exfalso; apply (H (sp - E)); lia|].
  destruct (Z_lt_le_dec x sp) as [L3|L3]; [exfalso; apply (H x); lia | exact L3].
Qed.

(* ---- the contract, in fm's post form ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis ROP : SV.ro_owned_pinned tfibsegs B.

Lemma pin_strncmp_core : forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
  ecall_pre tfibsegs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
  (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  PPgWrap.awrap_str tfibsegs W mem regs x ls -> PPgWrap.awrap_str tfibsegs W mem regs y rs ->
  amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
  SF.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
  WrapRo.aro_unowned tfibsegs B (aview tfibsegs (w_H W) mem) ->
  SRr tfibsegs W (cfg_at tfibsegs StrncmpDef.STRNCMP_ENTRY regs mem md)
    (rt_post_ro tfibsegs B STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> d = 0)).
Proof.
  intros ly S W regs mem md x y n ls rs d HEP HSLO HPRS G10 G11 G12 Hn S1 S2 AM1 AM2 HMOD HRO.
  pose proof HEP as (HAR & _).
  assert (HPRE : ecall_pre_k tfibsegs B STK_RT_STR ly S W regs mem md).
  { split; [exact HEP|]. split.
    - exact (lo_stk_ceil _ (am_layout _ _ _ _ (proj1 HAR))).
    - unfold StrncmpDef.FM_STK_RT_STR. split; [exact HSLO | exact HPRS]. }
  assert (HROM : rom_viewN tfibsegs B W mem) by exact HRO.
  assert (HROMO : rom_viewO tfibsegs B W mem) by exact (SV.fm_rom_viewO_of_AR tfibsegs B ly S W mem md ROP HAR).
  destruct S1 as (Hx0 & HxN & Hx32 & Hx63 & GA1 & SRC1 & WIN1 & AMR1 & RA1 & HV1 & TL1).
  destruct S2 as (Hy0 & HyN & Hy32 & Hy63 & GA2 & SRC2 & WIN2 & AMR2 & RA2 & HV2 & TL2).
  set (l1 := u8s ls) in *. set (l2 := u8s rs) in *.
  assert (LL1 : length l1 = length ls) by (unfold l1, u8s; apply length_map).
  assert (LL2 : length l2 = length rs) by (unfold l2, u8s; apply length_map).
  assert (CS1 : cstr tfibsegs W mem x l1) by (split; [exact GA1 | exact (u8s_ok ls HxN)]).
  assert (CS2 : cstr tfibsegs W mem y l2) by (split; [exact GA2 | exact (u8s_ok rs HyN)]).
  pose proof alloc_ceiling_lt as HCL.
  assert (Hxu : x + Z.of_nat (length ls) + 8 <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AM1; lia).
  assert (Hyu : y + Z.of_nat (length rs) + 8 <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AM2; lia).
  destruct (bytes_of_cstr W mem x l1 CS1 ltac:(lia) ltac:(rewrite LL1; lia)) as (BY1m & _ & F1).
  destruct (bytes_of_cstr W mem y l2 CS2 ltac:(lia) ltac:(rewrite LL2; lia)) as (BY2m & _ & F2).
  destruct (FMS.strncmp_strs n l1 l2 ltac:(lia) F1 F2) as (OK & SZ1 & SZ2 & RES).
  set (b1 := map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) in *.
  set (b2 := map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) in *.
  set (sz := SCS.strncmp_sz n b1 b2) in *.
  set (r := SCS.strncmp_res n b1 b2) in *.
  assert (CK1m : BQ.chk_ok (mrestrict (w_H W) mem) x sz).
  { apply (chk_ok_of_pre B ly S W mem md x sz HAR); [lia | rewrite LL1 in SZ1; lia | |
      apply (ra_prefix _ _ _ _ RA1); rewrite LL1 in SZ1; lia |
      intros Hs0; apply (hull_prefix _ _ _ _ HV1); rewrite LL1 in SZ1; lia].
    apply (amem_range_mono _ _ _ AM1). rewrite LL1 in SZ1. lia. }
  assert (CK2m : BQ.chk_ok (mrestrict (w_H W) mem) y sz).
  { apply (chk_ok_of_pre B ly S W mem md y sz HAR); [lia | rewrite LL2 in SZ2; lia | |
      apply (ra_prefix _ _ _ _ RA2); rewrite LL2 in SZ2; lia |
      intros Hs0; apply (hull_prefix _ _ _ _ HV2); rewrite LL2 in SZ2; lia].
    apply (amem_range_mono _ _ _ AM2). rewrite LL2 in SZ2. lia. }
  destruct (stk_of_pre B ly S W regs mem md STK_RT_STR HPRE ltac:(unfold StrncmpDef.FM_STK_RT_STR, ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  pose proof (rom_eq_of_views B W mem TB HROM HROMO) as RE.
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - STK_RT_STR) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - STK_RT_STR) (spZ regs));
      [unfold TFIB_IMG_END, YImgTop.IMG_TOP; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_sc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  assert (BY1 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x b1).
  { apply (bytes_at_clean _ x _ RE);
      [unfold b1; rewrite length_app, length_map; cbn [length]; rewrite LL1; unfold BM.UTOP; lia | exact BY1m]. }
  assert (BY2 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) y b2).
  { apply (bytes_at_clean _ y _ RE);
      [unfold b2; rewrite length_app, length_map; cbn [length]; rewrite LL2; unfold BM.UTOP; lia | exact BY2m]. }
  assert (CK1 : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x sz).
  { apply (chk_ok_clean _ x _ RE); [lia | rewrite LL1 in SZ1; lia | exact CK1m]. }
  assert (CK2 : BQ.chk_ok (clean (mrestrict (w_H W) mem)) y sz).
  { apply (chk_ok_clean _ y _ RE); [lia | rewrite LL2 in SZ2; lia | exact CK2m]. }
  assert (SEP1 : x + sz <= spZ regs - 2256 \/ spZ regs <= x).
  { apply (sep_of_win x (Z.of_nat (length ls)) (spZ regs) (2 * ESTACK) sz); [lia | rewrite LL1 in SZ1; lia |
      unfold ESTACK; lia | exact WIN1]. }
  assert (SEP2 : y + sz <= spZ regs - 2256 \/ spZ regs <= y).
  { apply (sep_of_win y (Z.of_nat (length rs)) (spZ regs) (2 * ESTACK) sz); [lia | rewrite LL2 in SZ2; lia |
      unfold ESTACK; lia | exact WIN2]. }
  assert (HDR : r = 0 <-> d = 0).
  { rewrite RES. symmetry. exact (model_zero ls rs n d ltac:(lia) HxN HyN HMOD). }
  set (lo := spZ regs - STK_RT_STR) in *.
  set (m := mrestrict (w_H W) mem) in *.
  eapply (bz_run_clean B TB W StrncmpDef.STRNCMP_ENTRY regs mem md _ _ HROM HROMO).
  - apply bz_canon. apply TRP.tramp_strncmp.
    eapply (SCW.istrncmp_spec RIP.rip_proof) with (p1 := x) (p2 := y) (n := n) (b1 := b1) (b2 := b2) (lo := lo).
    + exact G10.
    + exact G11.
    + exact G12.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo, StrncmpDef.FM_STK_RT_STR, ESTACK. lia.
    + unfold OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.A.R_m2s.kHighShadowEnd. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + lia.
    + exact BY1.
    + exact BY2.
    + exact OK.
    + lia.
    + lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact SEP1.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact SEP2.
    + exact CK1.
    + exact CK2.
    + exact M2S.
    + exact IC.
    + exact MI.
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    unfold SCP.istrncmp_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST').
    destruct (bz_window (clean m) m' (spZ regs) 2256 lo MU ST') as (MO & MN).
    { unfold lo, StrncmpDef.FM_STK_RT_STR, ESTACK. lia. }
    { unfold TFIB_IMG_END, YImgTop.IMG_TOP. lia. }
    eapply (rt_post_ro_win_clean B LAWS STK_RT_STR 2256 ly S W regs mem md _ _ ms' model' (r mod 2 ^ 64) HPRE).
    + unfold StrncmpDef.FM_STK_RT_STR, ESTACK. lia.
    + exact Hcl.
    + exact Heqv.
    + exact Hsbm.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + transitivity (Z_to_bv 64 r); [reflexivity|]. unfold w64. rewrite Z_to_bv64_mod. reflexivity.
    + apply Z.mod_pos_bound. lia.
    + rewrite <- HDR. pose proof (FMS.strncmp_res_range n b1 b2) as Hr. fold r in Hr.
      Z.div_mod_to_equations. lia.
    + exact MO.
    + exact MN.
Qed.

(* fm's post is PPgWrap's post: the answer word is 0 exactly when the model's answer is 0 *)
Lemma awrap_post_of_rt : forall ly S W regs mem md (d : Z) W' c',
  rt_post_ro tfibsegs B STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> d = 0) W' c' ->
  PPgWrap.awrap_post tfibsegs B ly S W regs mem md
    (fun regs' => exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) W' c'.
Proof.
  intros ly S W regs mem md d W' c'
    (-> & regs' & mem' & md' & v & Hc & HAR' & Hpres & Hsbm & G10 & Hv & HR & Hwin & Hp).
  unfold PPgWrap.awrap_post. split; [reflexivity|].
  exists regs', mem', md'.
  assert (HV0 : w64 v = w64 0 <-> d = 0).
  { rewrite <- HR. split; intros E; [|subst v; reflexivity].
    apply (f_equal bv_unsigned) in E. unfold w64 in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
    change (bv_modulus 64) with (2 ^ 64) in E. rewrite (Z.mod_small v) in E by lia. rewrite Z.mod_0_l in E by lia.
    exact E. }
  split; [exact Hc|]. split; [exact HAR'|]. split; [exact Hpres|]. split; [exact Hsbm|].
  split; [exists (w64 v); split; [exact G10 | exact HV0]|].
  split; [exact Hwin | exact Hp].
Qed.

End s.

(* ---- the top lemma: PPgWrap's text at pin's entry ---- *)
Theorem pin_astrncmp_A : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms),
  AR_laws tfibsegs B -> TfibSyms B -> SV.ro_owned_pinned tfibsegs B ->
  PPgWrap.astrncmp_realizes tfibsegs B 0x41914.
Proof.
  intros fx rc B LAWS TB ROP. unfold PPgWrap.astrncmp_realizes.
  intros ly S W regs mem md x y n ls rs d. intros.
  rewrite <- PC_strncmp_pin.
  eapply SRr_mono.
  - eapply (pin_strncmp_core B LAWS TB ROP ly S W regs mem md x y n ls rs d); eassumption.
  - intros W' c' _ HP. exact (awrap_post_of_rt B ly S W regs mem md d W' c' HP).
Qed.

(* every TfibSyms record: AR_laws holds of every symbol record (lib/Reusable/YG0q.v AR_laws_ok), and pin's
   tables pin the runtime-owned read-only bytes (lib/AU/Rt/PinRoPins.v) *)
Theorem pin_astrncmp : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms),
  TfibSyms B -> PPgWrap.astrncmp_realizes tfibsegs B 0x41914.
Proof.
  intros fx rc B TB.
  exact (pin_astrncmp_A B (YG0q.AR_laws_ok tfibsegs B) TB (PinRoPins.pin_ro_owned_pinned B TB)).
Qed.

(* pin's own symbol record (lib/AU/YD2l.v) *)
Theorem pin_astrncmp_TfibB : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  PPgWrap.astrncmp_realizes tfibsegs YD2l.TfibB 0x41914.
Proof. intros fx rc. exact (pin_astrncmp YD2l.TfibB YD2l.TfibB_syms). Qed.

Print Assumptions pin_astrncmp.
Print Assumptions pin_astrncmp_TfibB.
