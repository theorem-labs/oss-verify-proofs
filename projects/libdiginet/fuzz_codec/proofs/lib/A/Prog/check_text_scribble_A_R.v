(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_apply_state 0x82ed4 against lib/A/RPgCSpec.v's rl_cfg_apply_state_specX on the concrete image lib/A/Img0.v rsegs, with the plumbing of lib/A/RPgCfgChanges.v; the plain walk it replaces is lib/Prog/reac_role_cfg_apply_state.v (a split on the beq). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgCfgApply.v, with its module paths changed; 611 of its 636 lines of code are new or changed and 32 lines of the source are left out. *)
(* check_text_scribble at image A: the record point 0x83998 (cts_ss_rec) to the cut at 0x839b8, the
   return of diginet_scribble_text: the memset of the record to 0xa5, the call, the cut. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A.
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
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Lemma cts_rec_holds :
aintrin_realizes tfibsegs B OSet A_MEMSET -> cdc_scribble_text_specX tfibsegs B MT A_SCRIBBLE_TEXT ->
frame_flag_lawP tfibsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q,
cts_fctx B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 ->
(forall ly3 S3 W3 regs3 mem3 md3,
  cts_cut_ret B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj
    ly3 S3 W3 regs3 mem3 md3 fpos ->
  SRr tfibsegs W3 (cfg_at tfibsegs A_CTS_RET regs3 mem3 md3) Q) ->
cts_rec_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb S2 fpos SP1 E0 Q.
Proof using MTL MTF TL LAWS ML.
intros AMS SCR FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q
  HFC TAILQ.
destruct HFC as (HE & H10 & Hstr & Hoq & Hoch & H11 & Hdst & Hcjl & H12 & Hn & Hdisj & Howe & EE & E32
  & Hfrs2 & Eab & HMOsc & Hsp1 & Hsp1al).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal & Hwlo & Hwhi & Hev & Hlive).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble HE
  ltac:(unfold T_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof HJ0 as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_text_scribble, ESTACK in *.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & _).
assert (B2 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Hsp1al16 : SP1 mod 16 = 0)
  by (destruct (proj1 (Z.mod_divide SP1 32 ltac:(lia)) Hsp1al) as (kk & Hkk); rewrite Hkk;
      replace (kk * 32) with ((kk * 2) * 16) by lia; apply Z_mod_mult).
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
unfold cts_rec_cont.
intros EZ msZ mdZ HS SHOK AG E33 E38 E60 E61 E416 HJZ KT HIOc HWANTr.
change T_check_text_scribble with 8352 in KT.
pose proof HJZ as (HAR2 & _).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
pose proof (frm_off_img B lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as HFimg.
destruct (FFL lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2)
  as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLce)).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite (Z.div_mod F 64) at 1 by lia; rewrite HF64, Z.add_0_r;
      replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
destruct (al_frames _ _ LAWS lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HFal32 & _ & HFpres & HFSpres).
change (fs_frame_bytes 0) with 64 in HFpres, HFSpres. change (64 / 8) with 8 in HFSpres.
fold F in HFpres, HFSpres. fold FL in HFLown.
assert (HFno : forall a, F <= a < F + 64 -> ~ aowned B lyc S2 a)
  by (intros a Ha; exact (proj2 (HFpres a Ha))).
assert (HFSno : forall a, shadow_addr F <= a < shadow_addr F + 8 -> ~ aowned B lyc S2 a).
{ intros a Ha. pose proof (HFSpres (a - shadow_addr F) ltac:(lia)) as Hx.
  replace (shadow_addr F + (a - shadow_addr F)) with a in Hx by lia. exact (proj2 Hx). }
assert (HFLF : FL + 1 <= F \/ F + 64 <= FL)
  by (destruct (cw_flag_apart B lyc S2 FL F (F + 64) HFLown HFno) as [Hx|Hx]; [right | left]; lia).
assert (HFLS : FL + 1 <= shadow_addr F \/ shadow_addr F + 8 <= FL)
  by (destruct (cw_flag_apart B lyc S2 FL (shadow_addr F) (shadow_addr F + 8) HFLown HFSno) as [Hx|Hx];
      [right | left]; lia).
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFS : F + 64 <= shadow_addr F \/ shadow_addr F + 8 <= F).
{ unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
  destruct HFapp as (_ & [Hl | Hh]); [left | right]; lia. }
assert (HSlo : SHADOW_OFF + 512 <= shadow_addr F) by (unfold shadow_addr; lia).
assert (HShi : shadow_addr F + 8 <= SHADOW_OFF + 2 ^ 44 + 8) by (unfold shadow_addr; lia).
cw_hide HFLF. cw_hide HFLS. cw_hide HFS. cw_hide HFapp.
assert (HEimg : forall a, ch <= a < ch + 24 -> ~ in_img tfibsegs a).
{ intros a Ha Him. pose proof Hdst as (_ & _ & Htd & _).
  exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc ch 24 a HAR Htd Ha Him). }
assert (HZfr : forall a, (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL ->
  cw_fresh B lyc Sc a).
{ intros a Ha. apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    lyc S2 W (ms_mem msZ) mdZ k 0 fpos a HJ0 HJZ ltac:(rewrite Eab; apply Permutation_refl)).
  change (fs_frame_bytes 0) with 64. change (64 / 8) with 8.
  unfold frame_rng, in_zr. cbn [fst snd]. fold F FL. exact Ha. }
pose proof Hstr as (Hq0 & Hgtb & Hz0 & Hcrd).
pose proof Hcrd as (Hcq0 & Hcqhi & Hcrdb & Hcra & Hchull & Hcam & Hcwin).
assert (Htb1 : (1 <= length tb)%nat)
  by (destruct (length tb) eqn:EL; [destruct tb; [destruct Hz0 | discriminate EL] | lia]).
assert (HEch : forall x, q <= x < q + Z.of_nat (length tb) -> ~ (ch <= x < ch + 24))
  by (clear - Hdisj; intros x Hx Hc; lia).
assert (Hchfr : forall a, (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL ->
  ~ (ch <= a < ch + 24)).
{ intros a Ha Hin. destruct (HZfr a Ha) as (_ & _ & Hblk & Hfrm).
  destruct Hoch as [(b & m & Hb & Hlo & Hhi) | (cid & pos & Hb & Hlo & Hhi)].
  - exact (Hblk b m (a - b) Hb ltac:(lia) ltac:(lia)).
  - destruct (Hfrm cid pos Hb) as (Hzz & _). apply Hzz. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
pose proof Hdst as (Hch0 & Hchhi & Htd & Htwr & Hchra0 & Hchhull0 & Hcham & Hchwin).
unfold coff_win in Hchwin. unfold coff_win in Hcwin.
assert (HobjF : cobj_ok B lyc S2 F 64).
{ right. exists 0%Z, fpos. split; [rewrite Hfrs2; left; reflexivity|].
  change (fs_frame_bytes 0) with 64. lia. }
assert (HOLEN : length (fst (owed_scribble_text_spec tb n)) = Z.to_nat n)
  by (unfold owed_scribble_text_spec; apply cts_owe_len).
assert (HLEN : length (fst (scribble_text_spec tb n)) = Z.to_nat n)
  by (rewrite <- Howe; exact HOLEN).
assert (HOWN : In (0, fpos) ((0, fpos) :: own)) by (left; reflexivity).
    (* 0x83998-0x839a4: a1 = 165, a2 = 24, a0 = s4 = ch, jal __asan_memset *)
    cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
    cw_run_to cts_awr 0x51e34.
    lazymatch goal with
    | HFrw : frame_of ?Ev ?rs (mrestrict ?Hh ?ma) (mrestrict ?Hh ?mb) |- _ =>
      assert (HWa : forall j, 0 <= j < 8 ->
                aview tfibsegs Hh mb (F + 32 + j) = aview tfibsegs Hh ma (F + 32 + j));
      [ intros j Hj; unfold aview, mbyte;
        rewrite (HFrw (Z_to_bv 64 (F + 32 + j))); [reflexivity|];
        rewrite unsigned_lit_small by lia;
        let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
        intros (rr & Hin & Hb); cbv beta in Hb;
        lazymatch type of Hin with In _ ?rs0 =>
          let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hin end;
        repeat (destruct Hin as [<- | Hin];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]); destruct Hin
      | ] end.
    cts_keep F FL KT HAR HZfr. cts_rebase.
    (* the record's usable marks at the state of the call *)
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly4 ?S4 _ ?m4 _ _ |- _ =>
    assert (HRAch : range_addressable (aview tfibsegs (w_H W) m4) SHADOW_OFF ch 24)
      by (apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly4 S4 W m4 _ 8352 (spZ regs) (fun x => ch <= x < ch + 24)
            ch 24 HAR (proj1 HJx) ltac:(rewrite Eab; intros b m Hb; exact Hb)
            ltac:(intros cid pos; reflexivity) Hoch ltac:(clear - Hch0; lia) ltac:(clear; lia) Hchra0 KT
            ltac:(intros x Hx Hw; cbn beta in Hw;
                  exact (cts_shadow_apart x ch 24 ltac:(clear - Hch0 Hx; lia)
                    ltac:(clear - Hcham Hx; unfold amem_range in *; lia) Hcham ltac:(clear; lia) Hw))));
    assert (HHUch : shadow_hull_vis (aview tfibsegs (w_H W) m4) ch 24)
      by (apply (cts_obj_hull B LAWS lyc Sc S4 W m4 _ ch 24 (proj1 HJx)
            ltac:(rewrite Eab; intros b m Hb; exact Hb)
            ltac:(intros cid pos Hb; rewrite Hfrs2; right; exact Hb) Hoch ltac:(lia))) end.
    (* the atoms the regions are based on, in the state's own environment *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (M38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
    assert (M60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
    assert (M61 : bv_unsigned (ew Ev 61) = shadow_addr F)
      by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
    assert (M33 : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
    assert (M2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2);
    assert (M11 : ew Ev 11 = Z_to_bv 64 ch)
      by (rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11);
    assert (M3 : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl));
    assert (M4 : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)) end.
    pose proof E33 as E33n.
    repeat first [ rewrite ew_ewset_other in E33n by lia
                 | rewrite ew_havoc_old in E33n by (cbn; lia) ].
    rreg HS (2%bv : bv 5) RSP0. rewrite E33n in RSP0.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (HspM : spZ (ms_regs msx) = SP1)
      by (unfold spZ; rewrite RSP0; apply unsigned_lit_small; lia) end.
    pose proof M11 as M11b. cts_ebase M11b.
    pose proof M3 as M3b. cts_ebase M3b.
    pose proof M4 as M4b. cts_ebase M4b.
    rreg HS (10%bv : bv 5) RA0. rewrite M11b in RA0.
    rreg HS (11%bv : bv 5) RA1.
    rreg HS (12%bv : bv 5) RA2.
    rreg HS (3%bv : bv 5) RG3. rewrite M3b in RG3.
    rreg HS (4%bv : bv 5) RG4. rewrite M4b in RG4.
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let rsk := eval vm_compute in
      (List.filter (fun r => match YP09.r_base r with Some _ => true | None => false end) (ss_mem ssx)) in
    eapply (cw_intrin_call B LAWS OSet 0x51e34 AMS W Ev ssx msx _ STK sp0 FP ly S W0 mem0 md0 _ _ _ k
      ch 165 24 539048 500 rsk) end.
    1: exact HS.
    1: reflexivity.
    1: reflexivity.
    1: eassumption.
    1: first [exact RA0 | rewrite RA0; reflexivity].
    1: first [exact RA1 | rewrite RA1; vm_compute; reflexivity].
    1: first [exact RA2 | rewrite RA2; vm_compute; reflexivity].
    1: lia.
    1: lia.
    1: lia.
    1: (rewrite HspM; unfold ESTACK; lia).
    1: (rewrite HspM; lia).
    1: (rewrite HspM; exact Hsp1al16).
    1: exact Hsp0al.
    1: (rewrite RG3; exact Hgp).
    1: (rewrite RG4; exact Htp).
    1: (vm_compute; reflexivity).
    1: lia.
    1: (apply ret_ok_even; vm_compute; reflexivity).
    1: (intros a Ha; split;
        [ rewrite ?Eab;
          first [ exact (proj1 (Htwr a Ha)) | apply cts_awr_own; exact (proj1 (Htwr a Ha)) ]
        | rewrite HspM; unfold ESTACK; lia ]).
    1: exact Hcham.
    1: exact HRAch.
    1: (intros _; exact HHUch).
    1: exact I.
    1: (vm_compute; reflexivity).
    1: (vm_compute; reflexivity).
    1: (vm_compute; reflexivity).
    1: (vm_compute; reflexivity).
    1: (cbn [ss_mem]; submem_to).
    1: (repeat apply Forall_cons; try apply Forall_nil;
        (split;
        [ let a := fresh "a" in let Ha := fresh "Ha" in let Hx := fresh "Hx" in
          intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
          rewrite ?M60, ?M61, ?M38, ?M33, ?M2 in Ha;
          rewrite HspM; unfold ESTACK, SHADOW_OFF in *;
          split; [lia|];
          intros [Hx|Hx];
          [ first [ revert Hx; apply Hchfr; first [left; lia | right; left; lia | right; right; lia]
                  | lia ]
          | lia ]
        | cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; split; lia ])).
    cbv beta. intros regs4 mem4 md4 HJ4 HP4 RA4 Hset4 Hfr4 Hpres4 Hsm4 HS4.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msp) =>
    assert (HWb : forall j, 0 <= j < 8 ->
             aview tfibsegs (w_H W) mem4 (F + 32 + j)
             = aview tfibsegs (w_H W) (ms_mem msp) (F + 32 + j))
      by (intros j Hj; apply Hfr4;
          [ lia
          | intros Hy;
            assert (Hd : ~ (ch <= F + 32 + j < ch + 24)) by (apply Hchfr; left; lia);
            exact (Hd Hy)
          | rewrite HspM; unfold ESTACK; lia ]) end.
    norm_ss HS4. clear HS. rename HS4 into HS.
    (* what the call kept, folded into the walk's tcj_kept *)
    lazymatch goal with
      KTx : tcj_kept tfibsegs ?Bv ?T ?lycv ?Scv ?Wv ?memcv ?W1 ?m1 ?sp ?Ew |- _ =>
      pose proof (cw_kept_step Bv LAWS T lycv Scv Wv memcv _ W1 m1 mem4 sp Ew
        (fun a => (ch <= a < ch + 24) \/ (SP1 - ESTACK <= a < SP1))
        ltac:(unfold ESTACK; lia) HAR KTx
        ltac:(intros a Ha Hx; apply Hfr4;
              [ lia
              | intros Hy; apply Hx; left; exact Hy
              | rewrite HspM; intros Hy; apply Hx; right; exact Hy ])
        ltac:(intros a [Ha | Ha];
              [right; left; split; [exact Ha | exact (HEimg a Ha)]
              | left; unfold ESTACK in *; lia])
        ltac:(intros a Hp; apply Hpres4; exact Hp)) as KTn;
      clear KTx; rename KTn into KT
    end.
    lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
      assert (SHOK2 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor end.
    clear SHOK. rename SHOK2 into SHOK.
    cts_rebase. cw_norm_model.
    lazymatch type of Hsm4 with same_but_materialized ?mA _ =>
    assert (HIOm : same_io mdc md4)
      by (apply (same_io_trans mdc mA md4);
          [cpw_io | apply same_io_materialized; exact Hsm4]) end.
    (* the 24 bytes of the record are the fill byte; want is off the memset's range *)
    assert (Hrec : forall i, 0 <= i < 24 -> aview tfibsegs (w_H W) mem4 (ch + i) = Some 165)
      by (intros i Hi; exact (Hset4 i Hi)).

    (* 0x839a8-0x839b4: a0 = s5 = q, a1 = s4 = ch, a2 = s3 = n, jal diginet_scribble_text *)
    cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
    cw_run_to cts_awr 0x85cc4.
    (* the run writes nothing, so the record still holds the fill byte *)
    lazymatch goal with
    | HFr1 : frame_of ?Ev ?rs (mrestrict ?Hh ?ma) (mrestrict ?Hh ?mb) |- _ =>
      assert (Hrec5 : forall i, 0 <= i < 24 -> aview tfibsegs Hh mb (ch + i) = Some 165);
      [ intros i Hi; rewrite <- (Hrec i Hi); unfold aview, mbyte;
        rewrite (HFr1 (Z_to_bv 64 (ch + i))); [reflexivity|];
        rewrite unsigned_lit_small by lia;
        let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
        intros (rr & Hin & Hb); cbv beta in Hb;
        lazymatch type of Hin with In _ ?rs0 =>
          let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hin end;
        repeat (destruct Hin as [<- | Hin];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]); destruct Hin
      | ] end.
    lazymatch goal with
    | HFrw : frame_of ?Ev ?rs (mrestrict ?Hh ?ma) (mrestrict ?Hh ?mb) |- _ =>
      assert (HWc : forall j, 0 <= j < 8 ->
                aview tfibsegs Hh mb (F + 32 + j) = aview tfibsegs Hh ma (F + 32 + j));
      [ intros j Hj; unfold aview, mbyte;
        rewrite (HFrw (Z_to_bv 64 (F + 32 + j))); [reflexivity|];
        rewrite unsigned_lit_small by lia;
        let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
        intros (rr & Hin & Hb); cbv beta in Hb;
        lazymatch type of Hin with In _ ?rs0 =>
          let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hin end;
        repeat (destruct Hin as [<- | Hin];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]); destruct Hin
      | ] end.
    cts_keep F FL KT HAR HZfr. cts_rebase.
    (* the registers and the atoms at the call *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (N10 : ew Ev 10 = Z_to_bv 64 q)
      by (rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10);
    assert (N11 : ew Ev 11 = Z_to_bv 64 ch)
      by (rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11);
    assert (N12 : ew Ev 12 = Z_to_bv 64 n)
      by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12);
    assert (N3 : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl));
    assert (N4 : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)) end.
    pose proof N10 as N10b. cts_ebase N10b.
    pose proof N11 as N11b. cts_ebase N11b.
    pose proof N12 as N12b. cts_ebase N12b.
    pose proof N3 as N3b. cts_ebase N3b.
    pose proof N4 as N4b. cts_ebase N4b.
    pose proof E33 as E33m. cts_ebase E33m.
    rreg HS (1%bv : bv 5) S1r.
    rreg HS (2%bv : bv 5) S2r. rewrite E33m in S2r.
    rreg HS (3%bv : bv 5) S3r. rewrite N3b in S3r.
    rreg HS (4%bv : bv 5) S4r. rewrite N4b in S4r.
    rreg HS (10%bv : bv 5) SQr. rewrite N10b in SQr.
    rreg HS (11%bv : bv 5) SCr. rewrite N11b in SCr.
    rreg HS (12%bv : bv 5) SNr. rewrite N12b in SNr.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (HspN : spZ (ms_regs msx) = SP1)
      by (unfold spZ; rewrite S2r; apply unsigned_lit_small; lia) end.
    (* the text and the record at the state of the call *)
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly5 ?S5 _ ?m5 _ _ |- _ =>
    assert (HobjC : cobj_ok B ly5 S5 ch 24)
      by (apply (cts_obj_up B ly5 Sc S5 ch 24 ltac:(rewrite Eab; intros b m Hb; exact Hb)
                   ltac:(intros cid pos Hb; rewrite Hfrs2; right; exact Hb) Hoch));
    assert (HobjQ : cobj_ok B ly5 S5 q (Z.of_nat (length tb)))
      by (apply (cts_obj_up B ly5 Sc S5 q (Z.of_nat (length tb)) ltac:(rewrite Eab; intros b m Hb; exact Hb)
                   ltac:(intros cid pos Hb; rewrite Hfrs2; right; exact Hb) Hoq));
    assert (HRAq2 : range_addressable (aview tfibsegs (w_H W) m5) SHADOW_OFF q (Z.of_nat (length tb)))
      by (apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly5 S5 W m5 _ 8352 (spZ regs) (fun x => ch <= x < ch + 24)
            q (Z.of_nat (length tb)) HAR (proj1 HJx) ltac:(rewrite Eab; intros b m Hb; exact Hb)
            ltac:(intros cid pos; reflexivity) Hoq ltac:(lia) ltac:(lia) Hcra KT
            ltac:(intros x Hx Hw; cbn beta in Hw;
                  exact (cts_shadow_apart x ch 24 ltac:(clear - Hcq0 Hx; lia)
                    ltac:(clear - Hcam Hx; unfold amem_range in *; lia) Hcham ltac:(clear; lia) Hw))));
    assert (HHUq : shadow_hull_vis (aview tfibsegs (w_H W) m5) q (Z.of_nat (length tb)))
      by (apply (cts_obj_hull B LAWS lyc Sc S5 W m5 _ q (Z.of_nat (length tb)) (proj1 HJx)
            ltac:(rewrite Eab; intros b m Hb; exact Hb)
            ltac:(intros cid pos Hb; rewrite Hfrs2; right; exact Hb) Hoq ltac:(lia)));
    assert (Hgtb2 : YI00.garr8 tfibsegs (mrestrict (w_H W) m5) q tb)
      by (intros j Hj; destruct (Hgtb j Hj) as (Hv & Hr); split; [|exact Hr];
          apply (cts_obj_val B lyc Sc W memc W m5 8352 (spZ regs) (fun y => ch <= y < ch + 24)
            q (Z.of_nat (length tb)) (q + Z.of_nat j) 1%nat (nth j tb 0) Hoq ltac:(lia) ltac:(lia)
            ltac:(intros y Hy; exact (HEch y ltac:(lia))) KT Hv));
    assert (HRAc24 : range_addressable (aview tfibsegs (w_H W) m5) SHADOW_OFF ch 24)
      by (apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly5 S5 W m5 _ 8352 (spZ regs) (fun x => ch <= x < ch + 24)
            ch 24 HAR (proj1 HJx) ltac:(rewrite Eab; intros b m Hb; exact Hb)
            ltac:(intros cid pos; reflexivity) Hoch ltac:(lia) ltac:(lia) Hchra0 KT
            ltac:(intros x Hx Hw; cbn beta in Hw;
                  exact (cts_shadow_apart x ch 24 ltac:(clear - Hch0 Hx; lia)
                    ltac:(clear - Hcham Hx; unfold amem_range in *; lia) Hcham ltac:(clear; lia) Hw))));
    assert (HRAc2 : range_addressable (aview tfibsegs (w_H W) m5) SHADOW_OFF ch n)
      by (intros x Hx; apply HRAc24; lia);
    assert (HPRc : forall a, ch <= a < ch + 24 -> apresent (w_H W) m5 a /\ ~ aowned B ly5 S5 a)
      by (intros a Ha; exact (cts_obj_pres B LAWS ly5 S5 W m5 _ ch 24 a (proj1 HJx) HobjC Ha));
    assert (HPRq : forall a, q <= a < q + Z.of_nat (length tb) -> apresent (w_H W) m5 a)
      by (intros a Ha; exact (proj1 (cts_obj_pres B LAWS ly5 S5 W m5 _ q (Z.of_nat (length tb)) a
            (proj1 HJx) HobjQ Ha)));
    assert (HHUc2 : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) m5) ch n)
      by (intros Hn0; apply (cts_obj_hull B LAWS lyc Sc S5 W m5 _ ch n (proj1 HJx)
            ltac:(rewrite Eab; intros b m Hb; exact Hb)
            ltac:(intros cid pos Hb; rewrite Hfrs2; right; exact Hb)
            ltac:(apply (cts_obj_sub B lyc Sc ch 24); [exact Hoch | lia]) Hn0));
    idtac
    end.
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    eapply (cpw_call W Ev ssx msx _);
    [ exact HS
    | reflexivity
    | cbn [ss_pc ss_regs ss_mem];
      eapply (SCR STK sp0 FP ly S W0 mem0 md0 _ _ _ W (ms_mem msx) _ k (ms_regs msx)
                q ch n tb (repeat 165 (Z.to_nat n)))
    | ] end.
    1: (eapply cpw_entry;
        [ eassumption
        | rewrite S1r; apply ret_ok_even; vm_compute; reflexivity
        | unfold raZ; rewrite S1r, unsigned_lit_small by lia; lia
        | rewrite S3r; exact Hgp
        | rewrite S4r; exact Htp
        | rewrite HspN; exact Hsp1al16
        | rewrite HspN; unfold T_scribble_text, ESTACK; lia
        | rewrite HspN; lia
        | first [assumption | unfold EV_CDC in *; lia]
        | rewrite Eab; apply Permutation_refl
        | exact Hlive ]).
    1: exact SQr.
    1: (split; [lia|];
        split; [exact Hgtb2|];
        split; [exact Hz0|];
        split; [lia|];
        split; [lia|];
        split; [intros a Ha;
                first [apply (aview_some_of_apresent tfibsegs) | apply aview_some_of_apresent];
                exact (HPRq a Ha)|];
        split; [exact HRAq2|];
        split; [intros _; exact HHUq|];
        split; [exact Hcam
               | unfold coff_win in Hcwin |- *; rewrite HspN; unfold T_scribble_text, ESTACK; lia]).
    1: exact SCr.
    1: exact SNr.
    1: (split; [lia | rewrite repeat_length; lia]).
    1: (split; [lia|];
        split; [lia|];
        split; [ intros a Ha;
                 destruct (Htd a ltac:(lia)) as [(b & m & Hb & Hr)|(cid & pos & Hb & Hr)];
                 [ left; exists b, m; split; [rewrite Eab; exact Hb | exact Hr]
                 | right; exists cid, pos; split; [rewrite Hfrs2; right; exact Hb | exact Hr] ] |];
        split; [ intros a Ha; destruct (HPRc a ltac:(lia)) as (Hpa & Hoa);
                 split; [ rewrite Eab;
                          first [ exact (proj1 (Htwr a ltac:(lia)))
                                | apply cts_awr_own; exact (proj1 (Htwr a ltac:(lia))) ] |];
                 split; [exact Hpa|];
                 split; [exact Hoa | rewrite HspN; unfold ESTACK; lia ] |];
        split; [exact HRAc2|];
        split; [exact HHUc2|];
        split; [ unfold amem_range in *; lia
               | unfold coff_win; rewrite HspN; unfold T_scribble_text, ESTACK; lia ]).
    1: (intros j Hj; rewrite repeat_length in Hj;
        rewrite (nth_indep _ 0 165) by (rewrite repeat_length; lia);
        rewrite nth_repeat;
        split; [ apply AE36.val_mem1_of_aview; rewrite Hrec5 by lia; reflexivity | lia ]).
    1: lia.
    (* ---- the state the tail takes at 0x839b8 ---- *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Q38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
    assert (Q60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
    assert (Q61 : bv_unsigned (ew Ev 61) = shadow_addr F)
      by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
    assert (Q2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2);
    assert (Q33 : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
    assert (Q32 : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32)
    end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv26 : ew Ev 26 = getr regs 26)
      by (rewrite (AG 26%nat) by lia; exact (EE 26%nat 26%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv25 : ew Ev 25 = getr regs 25)
      by (rewrite (AG 25%nat) by lia; exact (EE 25%nat 25%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv24 : ew Ev 24 = getr regs 24)
      by (rewrite (AG 24%nat) by lia; exact (EE 24%nat 24%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv23 : ew Ev 23 = getr regs 23)
      by (rewrite (AG 23%nat) by lia; exact (EE 23%nat 23%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv22 : ew Ev 22 = getr regs 22)
      by (rewrite (AG 22%nat) by lia; exact (EE 22%nat 22%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv21 : ew Ev 21 = getr regs 21)
      by (rewrite (AG 21%nat) by lia; exact (EE 21%nat 21%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv20 : ew Ev 20 = getr regs 20)
      by (rewrite (AG 20%nat) by lia; exact (EE 20%nat 20%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv19 : ew Ev 19 = getr regs 19)
      by (rewrite (AG 19%nat) by lia; exact (EE 19%nat 19%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv18 : ew Ev 18 = getr regs 18)
      by (rewrite (AG 18%nat) by lia; exact (EE 18%nat 18%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv9 : ew Ev 9 = getr regs 9)
      by (rewrite (AG 9%nat) by lia; exact (EE 9%nat 9%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv8 : ew Ev 8 = getr regs 8)
      by (rewrite (AG 8%nat) by lia; exact (EE 8%nat 8%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Qv1 : ew Ev 1 = getr regs 1)
      by (rewrite (AG 1%nat) by lia; exact (EE 1%nat 1%bv eq_refl)) end.
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    destruct (cts_mem_at_rec (w_H W) Ev ssx msx regs (spZ regs) F FL HS
                ltac:(vm_compute; reflexivity) Q2 Q38 Q60 Q61
                ltac:(intros nn rr Hlt Hnr; rewrite (AG nn Hlt); exact (EE nn rr Hnr)))
      as (HSVm & HFLm & HSHm) end.
    (* a0 .. s11 at the call, and the used count *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Z2 : ew Ev 2 = getr regs 2) by (rewrite (AG 2%nat) by lia; exact (EE 2%nat 2%bv eq_refl));
    assert (Z27 : ew Ev 27 = getr regs 27)
      by (rewrite (AG 27%nat) by lia; exact (EE 27%nat 27%bv eq_refl));
    assert (Z32 : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
    cts_ebase Z2. cts_ebase Z27. cts_ebase Z32.
    pose proof E416 as E416b. cts_ebase E416b.
    pose proof E38 as E38b. cts_ebase E38b.
    pose proof E61 as E61b. cts_ebase E61b.
    rreg HS (26%bv : bv 5) SUr. rewrite E416b in SUr.
    rreg HS (8%bv : bv 5) S8r. rewrite Z2 in S8r.
    rreg HS (27%bv : bv 5) S27r. rewrite Z27 in S27r.
    rreg HS (18%bv : bv 5) S18r. rewrite E38b in S18r.
    rreg HS (25%bv : bv 5) S25r. rewrite E38b in S25r.
    rreg HS (19%bv : bv 5) S19r. rewrite N12b in S19r.
    rreg HS (20%bv : bv 5) S20r. rewrite N11b in S20r.
    rreg HS (21%bv : bv 5) S21r. rewrite N10b in S21r.
    rreg HS (22%bv : bv 5) S22r. rewrite E38b, unsigned_lit_small in S22r by lia.
    rreg HS (23%bv : bv 5) S23r. rewrite Z32 in S23r.
    rreg HS (24%bv : bv 5) S24r. rewrite E61b in S24r.
    rreg HS (9%bv : bv 5) S9r. rewrite E33m in S9r.
    cbv beta.
    intros Wc2 cfg2 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hfrs6 & HPerm6 & HIO6
                     & HMLE6 & KT6 & HA06 & HGc6).
    rewrite S1r.
    replace (k + EV_CDC) with k in HJ6 by (unfold EV_CDC; lia).
    rewrite HspN in KT6.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    (* what the callee kept of the frame, of its shadow and of the save area *)
    assert (HK6f : forall y, F <= y < F + 64 ->
            aview tfibsegs (w_H Wc2) mem6 y = aview tfibsegs (w_H W) (ms_mem msx) y)
      by (intros y Hy; exact (cts_obj_keep B lyc S2 W (ms_mem msx) Wc2 mem6 _ _ (fun x => ch <= x < ch + n) F 64 y HobjF Hy
            ltac:(cbn beta; intros Hzq; apply (Hchfr y (or_introl Hy)); lia) KT6));
    assert (HK6c : forall y, ch + n <= y < ch + 24 ->
            aview tfibsegs (w_H Wc2) mem6 y = aview tfibsegs (w_H W) (ms_mem msx) y)
      by (intros y Hy; exact (cts_obj_keep B lyc S2 W (ms_mem msx) Wc2 mem6 _ _ (fun x => ch <= x < ch + n) ch 24 y HobjC
            ltac:(lia) ltac:(cbn beta; lia) KT6));
    assert (HK6s : forall y, shadow_addr F <= y < shadow_addr F + 8 ->
            aview tfibsegs (w_H Wc2) mem6 y = aview tfibsegs (w_H W) (ms_mem msx) y);
    [ intros y Hy; pose proof KT6 as (_ & _ & _ & K4 & _);
      apply (K4 0 fpos y ltac:(rewrite Hfrs2; left; reflexivity));
      [ right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; fold F; lia
      | cbn beta; intros Hzq; apply (Hchfr y (or_intror (or_introl Hy))); lia ] | ];
    assert (HK6v : forall y, spZ regs - 96 <= y < spZ regs ->
            aview tfibsegs (w_H Wc2) mem6 y = aview tfibsegs (w_H W) (ms_mem msx) y);
    [ intros y Hy; pose proof KT6 as (K1 & _);
      exact (K1 y ltac:(lia) ltac:(unfold T_scribble_text, ESTACK; lia) ltac:(cbn beta; lia)) | ];
    (* the registers at the return *)
    assert (X2 : getr regs6 2 = Z_to_bv 64 SP1)
      by (etransitivity; [exact (HP6 2 ltac:(unfold acallee_saved; lia)) | exact S2r]);
    assert (X9 : getr regs6 9 = Z_to_bv 64 SP1)
      by (etransitivity; [exact (HP6 9 ltac:(unfold acallee_saved; lia)) | exact S9r]);
    assert (X8 : getr regs6 8 = getr regs 2)
      by (etransitivity; [exact (HP6 8 ltac:(unfold acallee_saved; lia)) | exact S8r]);
    assert (X3 : getr regs6 3 = getr regs 3)
      by (etransitivity; [exact (HP6 3 ltac:(unfold acallee_saved; lia)) | exact S3r]);
    assert (X4 : getr regs6 4 = getr regs 4)
      by (etransitivity; [exact (HP6 4 ltac:(unfold acallee_saved; lia)) | exact S4r]);
    assert (X18 : getr regs6 18 = Z_to_bv 64 F)
      by (etransitivity; [exact (HP6 18 ltac:(unfold acallee_saved; lia)) | exact S18r]);
    assert (X25 : getr regs6 25 = Z_to_bv 64 F)
      by (etransitivity; [exact (HP6 25 ltac:(unfold acallee_saved; lia)) | exact S25r]);
    assert (X19 : getr regs6 19 = Z_to_bv 64 n)
      by (etransitivity; [exact (HP6 19 ltac:(unfold acallee_saved; lia)) | exact S19r]);
    assert (X20 : getr regs6 20 = Z_to_bv 64 ch)
      by (etransitivity; [exact (HP6 20 ltac:(unfold acallee_saved; lia)) | exact S20r]);
    assert (X21 : getr regs6 21 = Z_to_bv 64 q)
      by (etransitivity; [exact (HP6 21 ltac:(unfold acallee_saved; lia)) | exact S21r]);
    assert (X22 : getr regs6 22 = Z_to_bv 64 (F + 32))
      by (etransitivity; [exact (HP6 22 ltac:(unfold acallee_saved; lia)) | exact S22r]);
    assert (X23 : getr regs6 23 = Z_to_bv 64 SB)
      by (etransitivity; [exact (HP6 23 ltac:(unfold acallee_saved; lia)) | exact S23r]);
    assert (X24 : getr regs6 24 = Z_to_bv 64 (shadow_addr F))
      by (etransitivity; [exact (HP6 24 ltac:(unfold acallee_saved; lia)) | exact S24r]);
    assert (X26 : getr regs6 26 = w64 (snd (owed_scribble_text_spec tb n)))
      by (etransitivity; [exact (HP6 26 ltac:(unfold acallee_saved; lia)) | exact SUr]);
    assert (X27 : getr regs6 27 = getr regs 27)
      by (etransitivity; [exact (HP6 27 ltac:(unfold acallee_saved; lia)) | exact S27r]);
    (* the memory the tail reads *)
    assert (CREC : YI00.garr8 tfibsegs (mrestrict (w_H Wc2) mem6) ch
             (fst (scribble_text_spec tb n) ++ repeat 165 (Z.to_nat (24 - n))));
    [ intros jj Hjj; rewrite app_length, repeat_length, HLEN in Hjj;
      destruct (lt_dec jj (Z.to_nat n)) as [Hlt|Hge];
      [ rewrite app_nth1 by lia; exact (HGc6 jj ltac:(lia))
      | rewrite app_nth2 by lia; rewrite HLEN;
        rewrite (nth_indep _ 0 165) by (rewrite repeat_length; lia); rewrite nth_repeat;
        split; [|lia];
        apply (cw_val_mem_kept (w_H W) (w_H Wc2) (ms_mem msx) mem6);
        [ intros y Hy; apply HK6c; lia
        | apply AE36.val_mem1_of_aview; rewrite Hrec5 by lia; reflexivity ] ] | ];
    assert (CWANT : YI00.garr8 tfibsegs (mrestrict (w_H Wc2) mem6) (F + 32)
             (fst (owed_scribble_text_spec tb n)));
    [ intros jj Hjj; rewrite HOLEN in Hjj;
      destruct (HWANTr jj ltac:(rewrite HOLEN; lia)) as (Hv & Hr); split; [|exact Hr];
      apply (cw_val_mem_kept (w_H W) (w_H Wc2) (ms_mem msx) mem6);
      [ intros y Hy; apply HK6f; lia |];
      apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ) (ms_mem msx));
      [ intros y Hy;
        replace y with (F + 32 + (y - (F + 32))) by lia;
        rewrite (HWc (y - (F + 32)) ltac:(lia)), (HWb (y - (F + 32)) ltac:(lia)),
                (HWa (y - (F + 32)) ltac:(lia));
        reflexivity
      | exact Hv ] | ];
    assert (CFL : val_mem tfibsegs (mrestrict (w_H Wc2) mem6) (F + 56) 8 FL)
      by (apply (cw_val_mem_kept (w_H W) (w_H Wc2) (ms_mem msx) mem6);
          [ intros y Hy; apply HK6f; lia | exact HFLm ]);
    assert (CSH : YI00.garr8 tfibsegs (mrestrict (w_H Wc2) mem6) (shadow_addr F) cts_shm_live);
    [ intros jj Hjj; destruct (HSHm jj Hjj) as (Hv & Hr); split; [|exact Hr];
      apply (cw_val_mem_kept (w_H W) (w_H Wc2) (ms_mem msx) mem6);
      [ intros y Hy; apply HK6s; cbn [length cts_shm_live] in Hjj; lia | exact Hv ] | ];
    assert (CSV : cts_saves (mrestrict (w_H Wc2) mem6) (spZ regs) regs);
    [ unfold cts_saves in HSVm |- *;
      destruct HSVm as (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26);
      repeat split;
      (apply (cw_val_mem_kept (w_H W) (w_H Wc2) (ms_mem msx) mem6);
       [ intros y Hy; apply HK6v; cbn [Z.of_nat] in Hy; lia | ]);
      [ exact V1 | exact V8 | exact V9 | exact V18 | exact V19 | exact V20
      | exact V21 | exact V22 | exact V23 | exact V24 | exact V25 | exact V26 ] | ]
    end.
    assert (HSP6 : spZ regs6 = SP1)
      by (unfold spZ; rewrite X2; apply unsigned_lit_small; lia).
    (* the cut, and the tail *)
    refine (TAILQ ly6 S6 Wc2 regs6 mem6 md6 _).
    unfold cts_cut_ret. cbv zeta.
    (* the frame's address and its flag byte do not depend on the layout the callee leaves *)
    assert (EFAf : frame_addr ly6 0 fpos = frame_addr lyc 0 fpos).
    { unfold frame_addr. pose proof HJ0 as (_ & Hly0 & _). pose proof HJ6 as (_ & Hly6 & _).
      destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
      destruct Hly6 as (_ & _ & _ & _ & _ & EF6 & _). rewrite EF0, EF6. reflexivity. }
    assert (EFAl : flag_addr ly6 0 fpos = flag_addr lyc 0 fpos).
    { unfold flag_addr. pose proof HJ0 as (_ & Hly0 & _). pose proof HJ6 as (_ & Hly6 & _).
      destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
      destruct Hly6 as (_ & _ & _ & _ & _ & EF6 & _). rewrite EF0, EF6. reflexivity. }
    rewrite EFAf, EFAl.
    split; [exact HE|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
    split; [exact Hn|]. split; [exact Hoch|]. split; [exact Hdst|]. split; [exact Hcjl|].
    split; [exact Howe|]. split; [exact HLEN|].
    split; [exact HJ6|].
    split; [rewrite Hfrs6, Hfrs2; left; reflexivity|].
    split; [rewrite Hfrs6; exact Hfrs2|].
    split; [rewrite <- Eab; exact HPerm6|].
    split; [eapply same_io_trans; [ | exact HIO6]; cpw_io|].
    split; [pose proof (mle_station MT Sc S2 S6 0 0 MTL HMOsc HMLE6) as HM;
            rewrite Z.add_0_r in HM; exact HM|].
    split; [ eapply (cw_kept_cj B LAWS) with (1 := HJ0) (2 := HJ4) (10 := KT) (11 := KT6);
             [ rewrite Hfrs2; apply incl_tl, incl_refl
             | rewrite Eab; apply Permutation_refl
             | lia | lia | unfold T_scribble_text, ESTACK; lia | lia
             | intros a Ha; cbn beta in Ha; right; left;
               split; [lia | exact (HEimg a ltac:(lia))] ] |].
    split; [rewrite HSP6; lia|].
    split; [rewrite HSP6; exact Hsp1al|].
    split; [rewrite X3; exact Hgp|]. split; [rewrite X4; exact Htp|].
    split; [exact X8|]. split; [rewrite X9, X2; reflexivity|].
    split; [exact HA06|].
    split; [exact X18|]. split; [exact X25|]. split; [exact X19|]. split; [exact X20|].
    split; [exact X21|]. split; [exact X22|]. split; [exact X23|]. split; [exact X24|].
    split; [exact X26|]. split; [exact X27|].
    split; [exact CREC|]. split; [exact CWANT|].
    split; [exact CFL|]. split; [exact CSH | exact CSV].
Qed.
End d.
End b.
