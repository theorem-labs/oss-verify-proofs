(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/SbDecSegB.v; 100 of its 306 lines of code are new or changed and 1725 lines of the source are left out. *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0), segment B, the case 100 <= v: three digits, three calls of
   sb_ch.  Statement: sbd_segB_v10b_spec (lib/B/Prog/SbDecSegB.v); proved here from SbDecSegB.v's Qed
   lemmas, in the shape of sbd_segB_lt10 there.
   The digit loop (0x836f4 .. 0x83734) runs three turns.  Its exit test bltu a3,a7 at 0x8372c fails on the
   first two turns (v >= 10 and v / 10 >= 10); on the third turn it ends the loop when v / 100 < 10
   (100 <= v < 1000), else the turn bound bltu a6,a5 at 0x83730 (a6 = 2) ends it (1000 <= v).  The two
   cases are the entry conditions [sbd_ge 21; sbd_ge 32; sbd_lt 33] and [sbd_ge 21; sbd_ge 32; sbd_ge 33];
   everything after the loop is the same: the pad's test bgeu a1,s4 at 0x83734 is taken (3 >= md, so no
   pad), and the run stops at the emit loop's head 0x83754 (BASE + 0x2fe0) with s4 = 2 and the digits
   v mod 10, v / 10 mod 10 and v / 100 mod 10 (+ 48) at F + 32 .. F + 34 (sbd_lh with i = 2, j = 0).
   SbDecSegB.v's sbd_emit_loop then walks the three turns of the emit loop, one sb_ch call each. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ IdentBProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC1g YC1h YC45 IdentBFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import sb_dec.
(* segment B's statements, cut predicates and Qed lemmas *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import SbDecSegB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HSC : tsb_ch_spec B.
Hypothesis PSIG : identb_prog_sig_ok.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The side goals of the run of the digit loop: its only write window is the digit slot [F + 32, F + 36)
   of sb_dec's frame (SbDecSegB.v's walk tactics sbd_wrange / sbd_awr / sbd_wr_slot / sbd_wr_img /
   sbd_pres_win / sbd_kvs, which are local to its section). *)
Ltac sbd_v10b_wrange Ha :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  destruct Ha as (r & Hr & Ha); vm_compute in Hr;
  destruct Hr as [Hr | [Hr | Hr]]; [ | | exfalso; exact Hr ];
  subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Ha end.
Ltac sbd_v10b_awr fp :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_v10b_wrange Ha; right; right; right;
  exists 0, fp;
  split; first [ left; reflexivity
               | left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia ].
Ltac sbd_v10b_wr_slot :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_v10b_wrange Ha; lia.
Ltac sbd_v10b_wr_img Hfi0 :=
  let a := fresh "a" in let Hi := fresh "Hi" in let Ha := fresh "Ha" in
  let Hi2 := fresh "Hi2" in let Hfi := fresh "Hfi" in
  intros a Hi Ha; pose proof (pa_img_range a Hi) as Hi2; pose proof Hfi0 as Hfi;
  change (fs_frame_bytes 0) with 64 in Hfi; sbd_v10b_wrange Ha; lia.
Ltac sbd_v10b_pres_win HJx :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _);
  apply Hpr; lia.
Ltac sbd_v10b_kvs HFr :=
  lazymatch type of HFr with
  | frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in let Hw := fresh "Hw" in
    intros a Ha Hn; apply (sbd_aview_frame _ m0 m1 (in_wrange E0 rs) a Ha);
    [ intros Hw; sbd_v10b_wrange Hw; apply Hn; clear - Hw; lia | exact HFr ]
  end.
(* The digit loop and the pad's test for 100 <= v, in both exit cases of the loop: from 0x836f4
   (BASE + 0x2f80) to the emit loop's head 0x83754 (BASE + 0x2fe0), where the state is sbd_lh with the
   turn index i = 2 and no digit emitted yet (j = 0, the struct's n and over as sb_dec found them). *)
Lemma sbd_v10b_head : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (regs : bvmap 5 word)
    (b v md p cap n ov : Z) (fpos : Z) (S2 : astate) (s1v : Z) (regs1 : bvmap 5 word) mem1 md1
    (Q : world SEGS -> config -> Prop),
  100 <= v ->
  sbd_at1 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
  (forall (regsL : bvmap 5 word) memL mdL,
     sbd_lh B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs b v md p cap n ov fpos S2 s1v mem1 2 0 n ov
       regsL memL mdL ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) regsL memL mdL) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x2f80) regs1 mem1 md1) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 Q
  Hv100 HAT HK.
pose proof HAT as HAT0.
destruct HAT0 as (HJ & Hfrs & Habl & Hra & Hal16 & Hwlo & Hwhi & Hgp & Htp & Hra4 & Hv & Hmd &
  Hb8 & Hb0 & Hb63 & Hbwin & Hrec & Hp & Hcap & Hn0 & Hn1 & Hov &
  Hs1lo & Hs1hi & Hs1al & Hflag &
  R2 & R3 & R4 & R5 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R18 & R19 & R20 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 &
  HSHB & VP & VCAP & VN & VOV & HWR & HROOM & HKEEP).
pose proof (proj1 HJ) as HAR.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HDS0 : SB_DEC_STK = 4256) by reflexivity.
assert (HCS0 : SB_CH_STK = 4112) by reflexivity.
assert (Hin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof pa_base_lo as HBLO.
destruct (frames_bounds SEGS B LAWS lyc S2 W mem1 md1 0 fpos HAR Hin) as (HF4096 & HFceil & HFapp).
(* where the caller's struct and sb_dec's stack window lie *)
pose proof HJ as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & Hstkz & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof Hrec as (Hrl0 & Hrh0).
assert (Hblo : alloc_ceiling <= b) by (rewrite Elo in Hrl0; lia).
assert (Hbhi : b + 32 <= 2 ^ 47) by (rewrite Ehi in Hrh0; lia).
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* the quotients of the three turns *)
assert (G1 : 10 <= v / 10) by (apply Z.div_le_lower_bound; lia).
assert (Q1 : 0 <= v / 10 < 2 ^ 31) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Q2 : 0 <= v / 10 / 10 < 2 ^ 31) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
(* the model: three digits, most significant first, and no pad (3 >= md) *)
assert (Hlsd : sb_dec_c.sb_dec_lsd v 3 = [48 + v mod 10; 48 + v / 10 mod 10; 48 + v / 10 / 10 mod 10]).
{ cbn [sb_dec_c.sb_dec_lsd].
  replace (v <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (v / 10 <? 10) with false by (symmetry; apply Z.ltb_ge; exact G1).
  destruct (v / 10 / 10 <? 10); reflexivity. }
assert (HDl : sb_dec_c.sb_dec_D v md = [48 + v / 10 / 10 mod 10; 48 + v / 10 mod 10; 48 + v mod 10]).
{ unfold sb_dec_c.sb_dec_D. rewrite Hlsd. cbn [length]. change (Z.of_nat 3) with 3.
  replace (3 <? md) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
(* the atoms of the entry state the run's facts and side conditions speak about *)
assert (EE21 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 21 = w64 v).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl). exact R21. }
assert (EE32 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 32 = Z_to_bv 64 (v / 10)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). }
assert (EE33 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 33 = Z_to_bv 64 (v / 10 / 10)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 1). }
assert (U25 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 25) = frame_addr lyc 0 fpos + 32).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl), R25. apply unsigned_lit_small. lia. }
assert (U38 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 38)
  = SHADOW_OFF + (frame_addr lyc 0 fpos + 32) / 8).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs1 _ 6). apply unsigned_lit_small.
  assert (HS8 : 0 <= (frame_addr lyc 0 fpos + 32) / 8) by (apply Z.div_pos; lia).
  assert (HS8h : (frame_addr lyc 0 fpos + 32) / 8 <= frame_addr lyc 0 fpos)
    by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF. lia. }
assert (EE2 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 2 = w64 s1v).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). exact R2. }
assert (EE3 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 3 = getr regs 3).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 3 3%bv eq_refl). exact R3. }
assert (EE4 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 4 = getr regs 4).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 4 4%bv eq_refl). exact R4. }
assert (EE8 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 8 = getr regs 2).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl). exact R8. }
assert (EE18 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 18 = w64 (frame_addr lyc 0 fpos)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl). exact R18. }
assert (EE19 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 19 = w64 b).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl). exact R19. }
assert (EE22 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 22 = w64 SHADOW_OFF).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl). exact R22. }
assert (EE23 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 23 = w64 (frame_addr lyc 0 fpos)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl). exact R23. }
assert (EE24 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 24
  = w64 (SHADOW_OFF + frame_addr lyc 0 fpos / 8)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 24 24%bv eq_refl). exact R24. }
assert (EE25 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 25 = w64 (frame_addr lyc 0 fpos + 32)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl). exact R25. }
assert (EE26 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 26
  = w64 (2 ^ 64 - (frame_addr lyc 0 fpos + 32) - 1)).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 26 26%bv eq_refl). exact R26. }
assert (EE27 : ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 27 = getr regs 27).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl). exact R27. }
assert (U35 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 35) = v mod 10).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 3).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound v 10 ltac:(lia)). lia. }
assert (U36 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 36) = v / 10 mod 10).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 4).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound (v / 10) 10 ltac:(lia)). lia. }
assert (U37 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 37) = v / 10 / 10 mod 10).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 5).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound (v / 10 / 10) 10 ltac:(lia)). lia. }
(* the shadow byte of the digit slot lies outside the slot, and the frame inside the address space *)
assert (HSHNS : 0 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < 2 ^ 64 /\
  ~ (frame_addr lyc 0 fpos + 32 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < frame_addr lyc 0 fpos + 36)).
{ pose proof (Z.div_mod (frame_addr lyc 0 fpos) 8 ltac:(lia)) as DF8.
  pose proof (Z.mod_pos_bound (frame_addr lyc 0 fpos) 8 ltac:(lia)) as MF8.
  unfold SHADOW_OFF. lia. }
assert (HFR : forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; lia).
(* the loop's two exit cases, as conditions of the entry state: the exit test fails on the first two
   turns; on the third it ends the loop (v / 100 < 10) or the turn bound does (v / 100 >= 10) *)
assert (HCASE :
  conds_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) [sbd_ge 21; sbd_ge 32; sbd_lt 33] \/
  conds_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) [sbd_ge 21; sbd_ge 32; sbd_ge 33]).
{ assert (C21 : acond_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) (sbd_ge 21))
    by exact (sbd_cond_ge _ 21 v ltac:(lia) EE21 ltac:(lia)).
  assert (C32 : acond_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) (sbd_ge 32))
    by exact (sbd_cond_ge _ 32 (v / 10) Q1 EE32 G1).
  destruct (Z.lt_ge_cases (v / 10 / 10) 10) as [H3 | H3].
  - left. split; [exact C21|]. split; [exact C32|]. split; [|exact I].
    exact (sbd_cond_lt _ 33 (v / 10 / 10) Q2 EE33 H3).
  - right. split; [exact C21|]. split; [exact C32|]. split; [|exact I].
    exact (sbd_cond_ge _ 33 (v / 10 / 10) Q2 EE33 H3). }
destruct HCASE as [HC | HC].
all: destruct (sbd_entry B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2
       s1v regs1 mem1 md1 _ HAT HC) as [HS SHOK].
all: remember (sbd_env regs1 v (frame_addr lyc 0 fpos)) as E eqn:HE.
all: assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sbd_env; apply Eimg_env).
all: unfold cfg_at; change (w64 (BASE + 0x2f80)) with (Z_to_bv 64 (BASE + 0x2f80)).
all: change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (BASE + 0x2f80)) mem1 (seg_rom SEGS))) in HJ.
(* the run from 0x836f4: three turns of the digit loop, the pad's test (taken: 3 >= md) and the emit
   loop's set-up, to its head 0x83754 *)
all: paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2fe0; [sbd_v10b_awr fpos | ].
all: rename ms into ms2; rename HFr into HFr2; rename HG into HG2; clear HF.
all: assert (K : tcj_kept B SB_CH_STK lyc Sc W mem1 W (ms_mem ms2) s1v
  (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36));
  [ eapply (sbd_kept_of_run B LAWS W _ _ mem1 (ms_mem ms2) lyc Sc S2 _ _ s1v SB_CH_STK);
    [ exact (proj1 HJ) | exact Habl | (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0)
    | exact HFr2 | exact HG2 | sbd_v10b_wr_slot
    | sbd_v10b_wr_img (frm_off_imgP B lyc S2 W mem1 md1 0 fpos HAR Hin) | sbd_v10b_pres_win HJ ]
  | ].
all: assert (KF : forall a, 0 <= a < 2 ^ 64 ->
  ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
  aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem1 a); [ sbd_v10b_kvs HFr2 | ].
(* the three digits the loop left in the slot, read back from the symbolic state *)
all: pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0.
all: destruct HR0 as (_ & _ & _ & HCH).
all: cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HCH.
all: rewrite U25 in HCH.
all: repeat (let Hk := fresh "HCk" in apply Forall_cons_iff in HCH; destruct HCH as [Hk HCH]).
all: repeat match goal with
     | H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff 35 48))) |- _ =>
         let Hd := fresh "HDG" in
         pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SOff 35 48) (48 + v mod 10) H
           ltac:(cbn [sv_denot]; rewrite U35; f_equal; apply Z.add_comm)
           ltac:(clear - Hv; pose proof (Z.mod_pos_bound v 10 ltac:(lia)); lia)) as Hd; clear H
     | H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff 36 48))) |- _ =>
         let Hd := fresh "HDG" in
         pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SOff 36 48) (48 + v / 10 mod 10) H
           ltac:(cbn [sv_denot]; rewrite U36; f_equal; apply Z.add_comm)
           ltac:(clear - Q1; pose proof (Z.mod_pos_bound (v / 10) 10 ltac:(lia)); lia)) as Hd; clear H
     | H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff 37 48))) |- _ =>
         let Hd := fresh "HDG" in
         pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SOff 37 48) (48 + v / 10 / 10 mod 10) H
           ltac:(cbn [sv_denot]; rewrite U37; f_equal; apply Z.add_comm)
           ltac:(clear - Q2; pose proof (Z.mod_pos_bound (v / 10 / 10) 10 ltac:(lia)); lia)) as Hd; clear H
     end.
(* the state at the loop head, as sbd_lh with i = 2 and j = 0 *)
all: pmkst HS.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Qg =>
       change (SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) rg mm mdx) Qg) end.
all: prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
     prreg HS (8%bv : bv 5) P8; prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19;
     prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22;
     prreg HS (23%bv : bv 5) P23; prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25;
     prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27.
all: apply HK.
all: unfold sbd_lh.
all: split; [lia|].
all: split; [rewrite HDl; reflexivity|].
all: split; [exact HJ|].
all: split; [rewrite P2, EE2; reflexivity|].
all: split; [rewrite P3, EE3; reflexivity|].
all: split; [rewrite P4, EE4; reflexivity|].
all: split; [rewrite P8, EE8; reflexivity|].
all: split; [rewrite P18, EE18; reflexivity|].
all: split; [rewrite P19, EE19; reflexivity|].
all: split; [rewrite P20; reflexivity|].
all: split; [rewrite P21; reflexivity|].
all: split; [rewrite P22, EE22; reflexivity|].
all: split; [rewrite P23, EE23; reflexivity|].
all: split; [rewrite P24, EE24; reflexivity|].
all: split; [rewrite P25, EE25; reflexivity|].
all: split; [rewrite P26, EE26; reflexivity|].
all: split; [rewrite P27, EE27; reflexivity|].
all: split;
  [ intros t Ht; rewrite HDl; destruct t as [|[|[|t]]]; try (exfalso; clear - Ht; lia);
    cbn [nth Nat.add Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ]; assumption | ].
all: split; [ intros a Ha Hn; exact (KF a (HFR a Ha) Hn) | ].
all: split; [ rewrite (KF _ (proj1 HSHNS) (proj2 HSHNS)); exact HSHB | ].
all: split;
  [ exact (sbd_inv0 B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
             regs1 mem1 md1 (ms_mem ms2) _ HAT HJ K)
  | apply (sbd_kept_mono B _ _ _ _ _ _ _ _ _ K); intros a Ha; left; exact Ha ].
Qed.
(* Segment B for 100 <= v: the digit loop and the pad's test (sbd_v10b_head), then the three turns of the
   emit loop (SbDecSegB.v's sbd_emit_loop from i = 2, j = 0). *)
Theorem sbd_segB_v10b : sbd_segB_v10b_spec B.
Proof.
unfold sbd_segB_v10b_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 Q
  Hv100 HAT HQ.
apply (sbd_v10b_head STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
         regs1 mem1 md1 Q Hv100 HAT).
intros regsL memL mdL HL.
exact (sbd_emit_loop B LAWS HSC PSIG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
         fpos S2 s1v regs1 mem1 md1 Q HAT HQ 2%nat 0%nat n ov regsL memL mdL HL).
Qed.
End walk.
End h.
End f.
End d.
