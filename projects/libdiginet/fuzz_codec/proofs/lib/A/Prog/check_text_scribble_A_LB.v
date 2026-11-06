(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, with its module paths changed; 260 of its 281 lines of code are new or changed and 301 lines of the source are left out. *)
(* The inlined owed_scribble_text loop of check_text_scribble at image A: the loop head 0x838d0 to 0x83908 (the
   text byte is not a dot) or through the dot's digit 0x838d8-0x83904. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A
check_text_scribble_A_LD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Lemma ctl_head_holds :
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q,
ctl_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 ->
ctl_join B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q ->
ctl_alt B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q ->
ctl_head B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q.
Proof using TL LAWS ML.
unfold ctl_head, ctl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q
  HPRE JOIN ALT EZ msZ mdZ o i pre HS HAT E417 E418 E419 Ho Hfuel Hi Hplen HMOD HWANT.
destruct HPRE as (HE & H10 & H11 & H12 & Hn & Hstr & Hoq & Hoch & Hdst & Hdisj & EE & E32
  & Hfin2 & Hfrs2 & Eab & HSP1 & HSP1al).
red in HAT. destruct HAT as (AG & E33 & E38 & E60 & E61 & HJ & KT & HIO).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HJ0) as HAR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble HE
  ltac:(unfold T_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_text_scribble, ESTACK in *.
pose proof (proj1 HJ) as HAR2.
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *.
assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HZfr : forall a, F <= a < F + 64 -> cw_fresh B lyc Sc a).
{ intros a Ha. apply (cw_fresh_own B LAWS lyc Sc lyc S2 W (ms_mem msZ) mdZ 0 fpos a HAR2 Hfrs2
    ltac:(rewrite Eab; apply Permutation_refl) ltac:(intros; reflexivity)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
assert (B2 : spZ regs = bv_unsigned (ew E0 2)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HF8m : F mod 8 = 0)
  by (destruct (proj1 (Z.mod_divide F 64 ltac:(lia)) HF64) as (kk & Hkk);
      replace F with (kk * 8 * 8) by lia; apply Z_mod_mult).
assert (HFam : amem_range F 64).
{ clear - HFapp C1 C2 C3 C4 C5.
  unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *. lia. }
assert (Htf : forall x, q <= x < q + Z.of_nat (length tb) -> ~ (F <= x < F + 64)).
{ intros x Hx Hinn. destruct (HZfr x Hinn) as (_ & _ & Hblk & Hfrm).
  destruct Hoq as [(bb & mm & Hb & Hlo & Hhi) | (cid & pos & Hb & Hlo & Hhi)].
  - exact (Hblk bb mm (x - bb) Hb ltac:(lia) ltac:(lia)).
  - destruct (Hfrm cid pos Hb) as (Hzz & _).
    exact (Hzz ltac:(unfold in_zr, frame_rng; cbn [fst snd]; lia)). }
pose proof Hstr as (Hq0 & Hgtb & Hin0 & Hcrd).
destruct (cts_cstring tb Hin0) as (Hzl & Hz0 & Hnz).
assert (Hilt : (Z.to_nat i < length tb)%nat) by lia.
destruct (Hgtb (Z.to_nat i) Hilt) as (_ & Hc8).
set (c := nth (Z.to_nat i) tb 0) in *.
(* the frame's flag byte lies off the four regions the loop carries: the head's own state says so *)
assert (U38z : bv_unsigned (ew EZ 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U61z : bv_unsigned (ew EZ 61) = shadow_addr F)
  by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U33z : bv_unsigned (ew EZ 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U2z : bv_unsigned (ew EZ 2) = spZ regs) by (rewrite (AG 2%nat) by lia; symmetry; exact B2).
assert (U60z : bv_unsigned (ew EZ 60) = ctl_FLu lyc fpos) by (rewrite E60; reflexivity).
assert (HFLD : ctl_fldisjZ F (ctl_FLu lyc fpos) SP1 (spZ regs))
  by exact (ctl_fldisj_of (w_H W) EZ cts_ss_lp msZ F (ctl_FLu lyc fpos) SP1 (spZ regs) HS
              ltac:(vm_compute; reflexivity) U60z U61z U38z U33z U2z).
clear U38z U61z U33z U2z U60z.
(* the flag byte's region is dropped while the loop puts a region on a text byte *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs' := eval vm_compute in (tl (ss_mem ssx)) in
  let HS1 := fresh "HS1" in
  pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS; norm_ss HS end.
pose proof HJ as HJn. clear HJ. rename HJn into HJ.
assert (SHOK : sh_ok tfibsegs CW_Bx [] EZ (mrestrict (w_H W) (ms_mem msZ))) by constructor.
assert (HWK : forall a, F + 32 <= a < F + 40 ->
  aview tfibsegs (w_H W) (ms_mem msZ) a = aview tfibsegs (w_H W) (ms_mem msZ) a) by (intros; reflexivity).
ctl_ufacts SP1 (spZ regs) E33 AG B2.
(* 0x838d0 zext.b a0,a5; stop at 0x838d4 bne a0,a3 *)
cw_run ctl_awr.
ctl_wkeep F. ctl_keep F HZfr.
cw_branch Hc.
all: ctl_c419 Hc.
- (* the text byte is not a dot *)
  assert (Hne : c <> 46) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc).
  cw_run_to ctl_awr 0x83908.
  ctl_wkeep F. ctl_keep F HZfr.
  cw_join_win HS ctl_ss_alt 470%nat cts_deadL_bv ltac:(idtac).
  ctl_rebase.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ => eapply (ALT Ev msx mdx o i pre) end end.
  1: exact HS.
  1: (red; split; [exact AG|]; split; [exact E33|]; split; [exact E38|]; split; [exact E60|];
      split; [exact E61|]; split; [eassumption|]; split; [exact KT | eapply same_io_trans; [exact HIO | cpw_io]]).
  1: exact E417. 1: exact E418. 1: exact E419.
  1: lia. 1: exact Hfuel. 1: lia. 1: exact HFLD. 1: exact Hplen. 1: exact HMOD.
  1: (intros (Hx & _); exact (Hne Hx)).
  1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
      apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ));
      [ intros y Hy; apply HWK; rewrite Hplen in Hjj; fold F; lia | exact Hvv ]).
- (* the text byte is a dot: the byte after it decides *)
  assert (Heq46 : c = 46) by (apply negb_false_iff, Z.eqb_eq in Hc; exact Hc).
  cw_run_to ctl_awr 0x838dc.
  ctl_wkeep F. ctl_keep F HZfr.
  ctl_rebase.
  pose proof Hcrd as (Hcq0 & Hcqhi & Hcrdb & Hcra & Hchull & Hcam & Hcwin).
  pose proof Hdst as (Hch0 & Hchhi & Htd & Htwr & Hchra0 & Hchhull0 & Hcham & Hchwin).
  unfold coff_win in Hcwin, Hchwin.
  assert (Hi1 : (Z.to_nat (i + 1) < length tb)%nat) by lia.
  set (c2 := nth (Z.to_nat (i + 1)) tb 0) in *.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (E10v : ew Ev 10 = Z_to_bv 64 q)
      by (rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10);
    assert (E32v : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly4 ?S4 _ ?m4 ?md4 _ |- _ =>
    destruct (ctl_text_at B LAWS lyc Sc W memc mdc ly4 S4 m4 md4 (spZ regs) q ch tb (Z.to_nat (i + 1))
      HAR (proj1 HJx) ltac:(rewrite Eab; intros bb mm Hb; exact Hb) ltac:(intros cid pos; reflexivity)
      Hstr Hoq Hcham Hch0 Hdisj KT Hi1) as (HRAq & HVq & Hc28) end.
  replace (q + Z.of_nat (Z.to_nat (i + 1))) with (q + 1 + i) in HVq by lia.
  assert (Hqhi : q + 1 + i <= 2 ^ 47 - 2)
    by (clear - Hcam Hi1 Hi Hcq0 C3 C4 C5; unfold amem_range in *; lia).
  assert (Hamx : amem_range (q + 1 + i) 1)
    by (clear - Hcam Hi1 Hi Hcq0; unfold amem_range in *; lia).
  (* the digit's address in atom 600 and its byte in atom 601 *)
  rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (q + 1 + i))
    (ctl_denot_of_U _ _ _ (ctl_add_off _ 10 1 418 q i E10v E418 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))
    R10.
  ctl_pin (10%bv : bv 5) 600%nat.
  ctl_rebase.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (E600 : ew Ev 600 = Z_to_bv 64 (q + 1 + i)) by (rewrite ctl_ew_h0; exact R10) end.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_add_fact tfibsegs Ev ssx msx 600%nat (mkAF 1 (2 ^ 47 - 2) 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E600, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; repeat split; first [lia | apply Z.mod_1_r])) as HS3;
    clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_havoc_win tfibsegs 601%nat Ev ssx msx [Z_to_bv 64 c2] HS
      ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end.
  ctl_rebase.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (E601 : ew Ev 601 = Z_to_bv 64 c2) by (rewrite ctl_ew_h0; reflexivity) end.
  ctl_ufacts SP1 (spZ regs) E33 AG B2.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (U38c : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
    assert (U61c : bv_unsigned (ew Ev 61) = shadow_addr F)
      by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia) end.
  assert (Hxoff : q + 1 + i + 1 <= F \/ F + 64 <= q + 1 + i)
    by (pose proof (Htf (q + 1 + i) ltac:(lia)); lia).
  assert (Hxsh : q + 1 + i + 1 <= shadow_addr F \/ shadow_addr F + 8 <= q + 1 + i)
    by (pose proof (ctl_text_off_fsh (q + 1 + i) F ltac:(lia) HF8m HFam
          Hamx ltac:(lia)); lia).
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
    pose proof (ast_ok_add_region tfibsegs Ev ssv msv
      (YP09.mkRegion (Some 600%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 601 0))]) HS eq_refl
      ltac:(unfold region_ok;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
            rewrite E600, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
            split; [intros oo Hoo; lia|];
            apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val tfibsegs Ev _ (q + 1 + i) 0 1 (SOff 601 0) c2);
            [rewrite sv_denot_SOff0, E601; reflexivity | cbn; lia | cbn; lia |];
            rewrite Z.add_0_r; exact (AE36.val_mem1_of_aview (w_H W) _ _ _ HVq))
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite E600, unsigned_lit_small by lia;
            repeat match goal with H : bv_unsigned (ew _ ?m) = _ |- _ =>
              lazymatch goal with |- context [bv_unsigned (ew _ m)] => rewrite H end end;
            repeat split; lia)) as HS3;
    clear HS; rename HS3 into HS end. norm_ss HS.
  repeat match goal with Hsh : sh_ok _ _ _ _ _ |- _ => clear Hsh end.
  lazymatch goal with HSx : st_ok _ ?Ev _ (restrict (w_H W) ?ms3) |- _ =>
    assert (Hdg : shent_ok tfibsegs CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) (mkSHE 600 0 1))
      by (apply (cw_shent_ra W (ms_mem ms3) Ev 600 (q + 1 + i) 1);
          [ intros x Hx; apply HRAq; lia
          | exact Hamx
          | lia | lia | lia | exact E600 | exact E32v ]);
    shok_auto_with SHOK CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) [mkSHE 600 0 1] ltac:(exact Hdg) end.
  ctl_ufacts SP1 (spZ regs) E33 AG B2.
  cw_run ctl_awr.
  ctl_wkeep F. ctl_keep F HZfr.
  cw_branch Hd.
  all: rewrite branch_ltu_U in Hd.
  all: lazymatch type of Hd with context [U ?Ecur (SAlu ALU_AND _ _)] =>
       let Hx := fresh "Hx" in
       assert (Hx : ew Ecur 601 = Z_to_bv 64 c2)
         by (repeat first [ solve [exact E601]
                          | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ]; exact E601);
       rewrite (ctl_digit_sub Ecur 601 c2 Hx Hc28) in Hd;
       rewrite (U_lit Ecur 8 ltac:(lia)) in Hd; clear Hx end.
  + (* the byte after the dot is no digit: the dot is stored as a plain byte *)
    assert (Hnd : ~ (49 <= c2 <= 57)).
    { intros Hdd. apply Z.ltb_lt in Hd.
      pose proof (proj2 (ctl_digit_iff c2 Hc28) Hdd). lia. }
    ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
    cw_run_to ctl_awr 0x83908.
    ctl_wkeep F. ctl_keep F HZfr.
    cw_join_win HS ctl_ss_alt 470%nat cts_deadL_bv ltac:(idtac).
    ctl_rebase.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
      lazymatch type of HS with st_ok _ ?Ev _ _ => eapply (ALT Ev msx mdx o i pre) end end.
    1: exact HS.
    1: (red; split; [exact AG|]; split; [exact E33|]; split; [exact E38|]; split; [exact E60|];
        split; [exact E61|]; split; [eassumption|];
        split; [exact KT | eapply same_io_trans; [exact HIO | cpw_io]]).
    1: exact E417. 1: exact E418. 1: exact E419.
    1: lia. 1: exact Hfuel. 1: lia. 1: exact HFLD. 1: exact Hplen. 1: exact HMOD.
    1: (intros (Hx1 & Hx2); exact (Hnd Hx2)).
    1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
        apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ));
        [ intros y Hy; apply HWK; rewrite Hplen in Hjj; fold F; lia | exact Hvv ]).
  + (* a digit: the dot and the digit become one byte and the turn uses two text bytes *)
    assert (Hdig : 49 <= c2 <= 57).
    { apply Z.ltb_ge in Hd. apply (proj1 (ctl_digit_iff c2 Hc28)). lia. }
    assert (Hi2 : i + 1 < Z.of_nat (length (cts_cstr tb))).
    { destruct (Z_lt_le_dec (i + 1) (Z.of_nat (length (cts_cstr tb)))) as [Hh|Hh]; [exact Hh | exfalso].
      assert (Hzz : c2 = 0).
      { change c2 with (nth (Z.to_nat (i + 1)) tb 0).
        replace (Z.to_nat (i + 1)) with (length (cts_cstr tb)) by lia. exact Hz0. }
      lia. }
    ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
    cw_run_to ctl_awr 0x83918.
    ctl_wkeep F. ctl_keep F HZfr.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      let Hx := fresh "Hx" in
      assert (Hx : ew Ev 601 = Z_to_bv 64 c2)
        by (repeat first [ solve [exact E601]
                         | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ]; exact E601);
      rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (c2 - 26))
        (ctl_denot_of_U Ev _ _ (ctl_sub26 Ev 601 c2 Hx ltac:(lia))) R15 end.
    rreg HS (16%bv : bv 5) R16.
    cw_join_win HS ctl_ss_join 490%nat ctl_deadJ_bv ltac:(idtac; ctl_join_hook).
    ctl_rebase.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (E460 : ew Ev 460 = Z_to_bv 64 (c2 - 26)) by (rewrite ctl_ew460; exact R15);
      assert (E461 : ew Ev 461 = Z_to_bv 64 2) by (rewrite ctl_ew461; exact R16) end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
      lazymatch type of HS with st_ok _ ?Ev _ _ => eapply (JOIN Ev msx mdx o i pre (c2 - 26) 2) end end.
    1: exact HS.
    1: (red; split; [exact AG|]; split; [exact E33|]; split; [exact E38|]; split; [exact E60|];
        split; [exact E61|]; split; [eassumption|];
        split; [exact KT | eapply same_io_trans; [exact HIO | cpw_io]]).
    1: exact E417. 1: exact E418. 1: exact E460. 1: exact E461.
    1: lia. 1: exact Hfuel. 1: lia. 1: lia. 1: (right; reflexivity). 1: lia. 1: exact HFLD. 1: exact Hplen.
    1: (replace (pre ++ [c2 - 26]) with (pre ++ [nth (Z.to_nat (i + 1)) tb 0 + -26])
          by (change c2 with (nth (Z.to_nat (i + 1)) tb 0); f_equal; f_equal; lia);
        replace (i + 2) with (2 + i) by lia;
        exact (cts_model_dot tb (Z.to_nat n) o i pre Hin0 HMOD ltac:(lia) ltac:(lia) Heq46 Hdig)).
    1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
        apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ));
        [ intros y Hy; apply HWK; rewrite Hplen in Hjj; fold F; lia | exact Hvv ]).
Qed.
End d.
End b.
