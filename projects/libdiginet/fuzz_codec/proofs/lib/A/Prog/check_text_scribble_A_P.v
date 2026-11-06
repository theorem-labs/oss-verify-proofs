(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_apply_state 0x82ed4 against lib/A/RPgCSpec.v's rl_cfg_apply_state_specX on the concrete image lib/A/Img0.v rsegs, with the plumbing of lib/A/RPgCfgChanges.v; the plain walk it replaces is lib/Prog/reac_role_cfg_apply_state.v (a split on the beq). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgCfgApply.v, with its module paths changed; 417 of its 442 lines of code are new or changed and 32 lines of the source are left out. *)
(* check_text_scribble at image A: the pad of want 0x83984 (cts_ss_pad) to the record point
   0x83998: want[o, n) filled with spaces by __asan_memset when o < n, nothing when o = n. *)
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

Lemma cts_pad_holds :
aintrin_realizes tfibsegs B OSet A_MEMSET -> frame_flag_lawP tfibsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q,
cts_fctx B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 ->
cts_rec_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb S2 fpos SP1 E0 Q ->
cts_pad_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb S2 fpos SP1 E0 Q.
Proof using MTL MTF TL LAWS ML.
intros AMS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj S2 fpos SP1 E0 Q
  HFC REC.
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
unfold cts_rec_cont in REC. change T_check_text_scribble with 8352 in REC.
unfold cts_pad_cont.
intros EZ msZ mdZ o i pre HS SHOK AG E33 E38 E60 E61 E417 E418 HJZ KT HIOc
       Hon Hi0 Hplen HMOD HMODi HWANTp.
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
    unfold cw_hold in HFapp.
    (* the frame's shadow bytes at this state, and want's usable marks from the zero shadow byte *)
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    assert (Q38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
    assert (Q60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
    assert (Q61 : bv_unsigned (ew Ev 61) = shadow_addr F)
      by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
    assert (Q2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2);
    destruct (cts_mem_at_rec (w_H W) Ev ssx msx regs (spZ regs) F FL HS
                ltac:(vm_compute; reflexivity) Q2 Q38 Q60 Q61
                ltac:(intros nn rr Hlt Hnr; rewrite (AG nn Hlt); exact (EE nn rr Hnr)))
      as (HSVm & HFLm & HSHm) end.
    assert (HF8m : F mod 8 = 0)
      by (destruct (proj1 (Z.mod_divide F 64 ltac:(lia)) HF64) as (kk & Hkk);
          replace F with (kk * 8 * 8) by lia; apply Z_mod_mult).
    assert (HSH4 : aview tfibsegs (w_H W) (ms_mem msZ) (shadow_addr F + 4) = Some 0).
    { destruct (HSHm 4%nat ltac:(cbn; lia)) as (Hv & _).
      pose proof (Hv 0%nat ltac:(lia)) as Hb.
      replace (shadow_addr F + Z.of_nat 4 + Z.of_nat 0) with (shadow_addr F + 4) in Hb by lia.
      unfold aview. rewrite Hb. vm_compute; reflexivity. }
    assert (HRAw : range_addressable (aview tfibsegs (w_H W) (ms_mem msZ)) SHADOW_OFF (F + 32) 8).
    { apply (zero_shadow_range (aview tfibsegs (w_H W) (ms_mem msZ)) SHADOW_OFF (F + 32) 8).
      - replace (F + 32) with ((F / 8 + 4) * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
        apply Z_mod_mult.
      - reflexivity.
      - intros ii Hii. change (8 / 8) with 1 in Hii. replace ii with 0 by lia.
        rewrite Z.add_0_r.
        assert (Heq : shadow_of_addr SHADOW_OFF (F + 32) = shadow_addr F + 4)
          by (unfold shadow_of_addr, shadow_addr;
              replace ((F + 32) / 8) with (F / 8 + 4)
                by (rewrite <- (Z.div_add F 4 8 ltac:(lia)); f_equal; lia); lia).
        rewrite Heq. exact HSH4. }
    (* 0x83984 bgeu a1,s3: o >= n skips the pad, o < n fills want[o, n) with spaces *)
    cw_branch Hpad.
    - (* o >= n, and o <= n, so want already holds all n characters *)
      (let Hn12 := fresh "Hn12" in
       assert (Hn12 : ew EZ 12 = Z_to_bv 64 n)
         by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12);
       rewrite branch_geu_U in Hpad;
       rewrite (U_atom_off EZ 12 n 0 Hn12) in Hpad by lia;
       rewrite (U_atom_off EZ 417 o 0 E417) in Hpad by lia;
       rewrite ?Z.add_0_r in Hpad; clear Hn12).
      assert (Hoeq : o = n)
        by (assert (Hge : n <= o) by (apply Z.ltb_ge, negb_true_iff; exact Hpad); lia).
      assert (HWfull : fst (owed_scribble_text_spec tb n) = pre)
        by (rewrite HMOD, Hoeq; replace (Z.to_nat n - Z.to_nat n)%nat with 0%nat by lia;
            cbn [repeat]; apply app_nil_r).
      cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
      cw_run_to cts_awr 0x83998.
      lazymatch goal with
      | HFrw : frame_of ?Ev ?rs (mrestrict ?Hh ?ma) (mrestrict ?Hh ?mb) |- _ =>
        assert (HWp : forall j, 0 <= j < 8 ->
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
      pose proof E418 as E418b. cts_ebase E418b.
      rreg HS (26%bv : bv 5) SU0. rewrite E418b in SU0.
      cw_join_win HS cts_ss_rec 400%nat cts_deadR_bv ltac:(idtac).
      lazymatch type of HS with st_ok _ (havoc ?Ev 400 ?vals) _ (restrict _ ?msx) =>
      assert (E416n : ew (havoc Ev 400 vals) 416 = w64 (snd (owed_scribble_text_spec tb n)));
      [ change 416%nat with (400 + 16)%nat;
        rewrite (ew_havoc_new Ev 400 vals 16 (Z_to_bv 64 0) ltac:(cbn; lia));
        cbn [nth map cts_deadR_bv]; rewrite SU0, HMODi; reflexivity | ] end.
      eapply REC.
      1: exact HS.
      1: (lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
          assert (SH2 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor;
          exact SH2 end).
      1: (intros nn Hnn; rewrite ew_havoc_old by (cbn; lia); apply AG; lia).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E33).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E38).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E60).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E61).
      1: exact E416n.
      1: eassumption.
      1: exact KT.
      1: (eapply same_io_trans; [exact HIOc | cpw_io]).
      1: (rewrite HWfull; intros jj Hjj;
          destruct (HWANTp jj Hjj) as (Hv & Hr); split; [|exact Hr];
          apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ));
          [ intros y Hy; replace y with (F + 32 + (y - (F + 32))) by lia;
            rewrite (HWp (y - (F + 32)) ltac:(rewrite Hplen in Hjj; lia)); reflexivity
          | exact Hv ]).
    - (* o < n: the pad fills want[o, n) with spaces *)
      (let Hn12 := fresh "Hn12" in
       assert (Hn12 : ew EZ 12 = Z_to_bv 64 n)
         by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12);
       rewrite branch_geu_U in Hpad;
       rewrite (U_atom_off EZ 12 n 0 Hn12) in Hpad by lia;
       rewrite (U_atom_off EZ 417 o 0 E417) in Hpad by lia;
       rewrite ?Z.add_0_r in Hpad; clear Hn12).
      assert (Holt : o < n)
        by (apply Z.ltb_lt, negb_false_iff; exact Hpad).
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (E12p : ew Ev 12 = Z_to_bv 64 n)
        by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12) end.
      assert (HShv : shadow_addr F + 8 <= 2147450880 + 2 ^ 44 + 8) by (unfold SHADOW_OFF in HShi; lia).
      (* 0x83988-0x83994: a0 = want + o, a2 = n - o, a1 = 32, jal __asan_memset *)
      cts_ufacts F FL SP1 (spZ regs) E38 E60 E61 E33 AG B2.
      cw_run_to cts_awr 0x51e34.
      (* the run writes nothing: want's bytes and want's shadow byte are those of the pad point *)
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
        | ];
        assert (HWs : aview tfibsegs Hh mb (shadow_addr F + 4) = aview tfibsegs Hh ma (shadow_addr F + 4));
        [ unfold aview, mbyte;
          rewrite (HFrw (Z_to_bv 64 (shadow_addr F + 4))); [reflexivity|];
          rewrite unsigned_lit_small by (clear - HSlo HShv; unfold SHADOW_OFF in HSlo; lia);
          let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
          intros (rr & Hin & Hb); cbv beta in Hb;
          lazymatch type of Hin with In _ ?rs0 =>
            let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hin end;
          repeat (destruct Hin as [<- | Hin];
                  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]); destruct Hin
        | ] end.
      cts_keep F FL KT HAR HZfr. cts_rebase.
      pose proof E33 as E33m. cts_ebase E33m.
      rreg HS (2%bv : bv 5) RSP0. rewrite E33m in RSP0.
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
      assert (HspM : spZ (ms_regs msx) = SP1)
        by (unfold spZ; rewrite RSP0; apply unsigned_lit_small; lia) end.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (M38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
      assert (M60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
      assert (M61 : bv_unsigned (ew Ev 61) = shadow_addr F)
        by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
      assert (M33 : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
      assert (M2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2);
      assert (M3 : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl));
      assert (M4 : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl));
      idtac end.
      lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      let e10 := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
      assert (RA0 : getr (ms_regs msx) (10%bv : bv 5) = Z_to_bv 64 (F + 32 + o));
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (10%bv : bv 5) HS) _);
        change (sv_denot Ev e10 = Z_to_bv 64 (F + 32 + o));
        rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw];
        rewrite (U_atom_off Ev 38 F 32 E38) by lia;
        rewrite (U_atom_off Ev 417 o 0 E417) by lia;
        rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia | ] end.
      lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      let e12 := eval vm_compute in (sr_get (ss_regs ssx) (12%bv : bv 5)) in
      assert (RA2 : getr (ms_regs msx) (12%bv : bv 5) = Z_to_bv 64 (n - o));
      [ refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx (12%bv : bv 5) HS) _);
        change (sv_denot Ev e12 = Z_to_bv 64 (n - o));
        rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw];
        rewrite U_SMd; cbn [zmd_raw];
        rewrite (U_atom_off Ev 12 n 0 E12p) by lia;
        rewrite (U_atom_off Ev 417 o 0 E417) by lia;
        rewrite U_SLit; unfold zcanon;
        rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_r;
        replace (n + 0 + (o + 0) * -1) with (n - o) by lia;
        apply Z.mod_small; unfold M64; lia | ] end.
      pose proof M3 as M3b. cts_ebase M3b.
      pose proof M4 as M4b. cts_ebase M4b.
      rreg HS (11%bv : bv 5) RA1.
      rreg HS (3%bv : bv 5) RG3. rewrite M3b in RG3.
      rreg HS (4%bv : bv 5) RG4. rewrite M4b in RG4.
      (* want[o, n): its shadow window is readable (a frame of the walk's state) and its bytes are marked
         usable (want's shadow byte is 0, as at the pad point) *)
      assert (HFq8 : F = 8 * (F / 8))
        by (pose proof (Z.div_mod F 8 ltac:(lia)) as Hdm; rewrite HF8m in Hdm; lia).
      lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m4 ?md4 _ |- _ =>
      assert (HHUw : shadow_hull_vis (aview tfibsegs (w_H W) m4) (F + 32 + o) (n - o))
        by (apply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc S2 W m4 md4 0 fpos);
            [ exact (proj1 HJx) | exact Hfin2
            | fold F; lia | change (fs_frame_bytes 0) with 64; fold F; lia | lia ]);
      assert (HRAw2 : range_addressable (aview tfibsegs (w_H W) m4) SHADOW_OFF (F + 32 + o) (n - o))
        by (intros x Hx;
            assert (Hxd : x / 8 = F / 8 + 4)
              by (replace x with (8 * (F / 8 + 4) + (x - F - 32)) by lia;
                  rewrite (Z.mul_comm 8 (F / 8 + 4)), Z.div_add_l by lia;
                  rewrite (Z.div_small (x - F - 32) 8) by lia; lia);
            assert (Hsx : shadow_of_addr SHADOW_OFF x = shadow_addr F + 4)
              by (unfold shadow_of_addr, shadow_addr; rewrite Hxd; lia);
            destruct (HRAw x ltac:(lia)) as (sv & Hsv & Hok); exists sv; split; [|exact Hok];
            rewrite Hsx in Hsv |- *; rewrite HWs; exact Hsv) end.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdg) _ =>
      lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      let rsk := eval vm_compute in (ss_mem ssx) in
      eapply (cw_intrin_call B LAWS OSet 0x51e34 AMS W Ev ssx msx mdg STK sp0 FP ly S W0 mem0 md0 _ _ _ k
        (F + 32 + o) 32 (n - o) 539032 600 rsk) end end.
      1: exact HS.
      1: reflexivity.
      1: reflexivity.
      1: eassumption.
      1: first [exact RA0 | rewrite RA0; reflexivity].
      1: first [exact RA1 | rewrite RA1; vm_compute; reflexivity].
      1: first [exact RA2 | rewrite RA2; reflexivity].
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
          [ right; right; right; exists 0%Z, fpos; split; [left; reflexivity|];
            left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia
          | rewrite HspM; unfold ESTACK; lia ]).
      1: (clear - HFapp Holt Hon Hn C1;
          unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia).
      1: exact HRAw2.
      1: (intros _; exact HHUw).
      1: exact I.
      1: (vm_compute; reflexivity).
      1: (vm_compute; reflexivity).
      1: (vm_compute; reflexivity).
      1: (vm_compute; reflexivity).
      1: (cbn [ss_mem]; submem_to).
      1: (unfold cw_hold in HFLF, HFS;
          repeat apply Forall_cons; try apply Forall_nil;
          (split;
          [ let a := fresh "a" in let Ha := fresh "Ha" in let Hx := fresh "Hx" in
            intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
            rewrite ?M60, ?M61, ?M38, ?M33, ?M2 in Ha;
            rewrite HspM; unfold ESTACK, SHADOW_OFF in *;
            split; [lia|];
            intros [Hx|Hx]; lia
          | cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; split; lia ])).
      cbv beta. intros regs4 mem4 md4 HJ4 HP4 RA4 Hset4 Hfr4 Hpres4 Hsm4 HS4.
      (* want[0, o) is kept by the memset, want[o, n) holds spaces *)
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?msp) =>
      assert (HWb : forall j, 0 <= j < o ->
               aview tfibsegs (w_H W) mem4 (F + 32 + j)
               = aview tfibsegs (w_H W) (ms_mem msp) (F + 32 + j))
        by (intros j Hj; apply Hfr4; [ lia | lia | rewrite HspM; unfold ESTACK; lia ]) end.
      assert (Hspc : forall j, 0 <= j < n - o -> aview tfibsegs (w_H W) mem4 (F + 32 + o + j) = Some 32)
        by (intros j Hj; exact (Hset4 j Hj)).
      norm_ss HS4. clear HS. rename HS4 into HS.
      lazymatch goal with
        KTx : tcj_kept tfibsegs ?Bv ?T ?lycv ?Scv ?Wv ?memcv ?W1 ?m1 ?sp ?Ew |- _ =>
        pose proof (cw_kept_step Bv LAWS T lycv Scv Wv memcv _ W1 m1 mem4 sp Ew
          (fun a => (F + 32 + o <= a < F + 32 + o + (n - o)) \/ (SP1 - ESTACK <= a < SP1))
          ltac:(unfold ESTACK; lia) HAR KTx
          ltac:(intros a Ha Hx; apply Hfr4;
                [ lia
                | intros Hy; apply Hx; left; exact Hy
                | rewrite HspM; intros Hy; apply Hx; right; exact Hy ])
          ltac:(intros a [Ha | Ha];
                [ right; right; apply HZfr; left; lia
                | left; unfold ESTACK in *; lia ])
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
      (* the record point: the state is there; join it into cts_ss_rec, then the continuation *)
      pose proof E418 as E418b. cts_ebase E418b.
      rreg HS (26%bv : bv 5) SU0. rewrite E418b in SU0.
      cbn [ms_regs restrict mkst] in SU0.
      cw_join_win HS cts_ss_rec 400%nat cts_deadR_bv ltac:(idtac).
      lazymatch type of HS with st_ok _ ?Ewhole _ _ =>
      assert (E416n : ew Ewhole 416 = w64 (snd (owed_scribble_text_spec tb n)));
      [ change 416%nat with (400 + 16)%nat;
        rewrite (ew_havoc_new _ _ _ _ (Z_to_bv 64 0)) by (cbn; lia);
        cbn [nth map cts_deadR_bv ms_regs restrict mkst];
        rewrite SU0, HMODi; reflexivity | ] end.
      eapply REC.
      1: exact HS.
      1: (lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
          assert (SH2 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor;
          exact SH2 end).
      1: (intros nn Hnn; rewrite ew_havoc_old by (cbn; lia); apply AG; lia).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E33).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E38).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E60).
      1: (rewrite ew_havoc_old by (cbn; lia); exact E61).
      1: exact E416n.
      1: eassumption.
      1: exact KT.
      1: (eapply same_io_trans; [exact HIOm | cpw_io]).
      1: (rewrite HMOD; intros jj Hjj; rewrite app_length, repeat_length in Hjj;
          destruct (lt_dec jj (Z.to_nat o)) as [Hlt|Hge];
          [ rewrite app_nth1 by lia;
            destruct (HWANTp jj ltac:(lia)) as (Hv & Hr); split; [|exact Hr];
            apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ) mem4);
            [ intros y Hy; cbn [Z.of_nat] in Hy;
              replace y with (F + 32 + (y - (F + 32))) by lia;
              rewrite (HWb (y - (F + 32)) ltac:(lia)), (HWa (y - (F + 32)) ltac:(lia)); reflexivity
            | exact Hv ]
          | rewrite app_nth2 by lia;
            rewrite (nth_indep _ 0 32) by (rewrite repeat_length; lia); rewrite nth_repeat;
            split; [|lia];
            apply AE36.val_mem1_of_aview;
            replace (F + 32 + Z.of_nat jj) with (F + 32 + o + (Z.of_nat jj - o)) by lia;
            apply Hspc; lia ]).
Qed.
End d.
End b.
