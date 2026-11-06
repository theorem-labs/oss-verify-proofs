(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/SbDecSegB.v; 105 of its 251 lines of code are new or changed and 1785 lines of the source are left out. *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0), segment B, the case 10 <= v < 100: two digits, two calls of
   sb_ch.  The statement sbd_segB_v10a_spec and everything this file uses are lib/B/Prog/SbDecSegB.v's.
   The walk, from the neutral listing:
   - 0x836f4..0x83734 the digit loop, two turns: the first turn stores d[0] = v mod 10 + 48 at F + 32 and
     does not take the exit test bltu a3,a7 at 0x8372c (10 <= v: the entry condition sbd_ge 21), then takes
     bltu a6,a5 at 0x83730 back (a6 = 0 < a5 = 2); the second turn stores d[1] = v / 10 mod 10 + 48 at
     F + 33 and takes the exit test (v / 10 < 10: the entry condition sbd_lt 32);
   - 0x83734 bgeu a1,s4 with a1 = 2 and s4 = md in [1, 2]: always taken, so the pad 0x83738..0x83748 and
     its UBSan null check beq s9,a0 at 0x8373c are never executed on this path;
   - 0x8374c..0x83750 s4 := a0 - 1 = 1, s5 := -1, which is the emit loop's head 0x83754 (BASE + 0x2fe0) with
     index i = 1 and no digit emitted yet (j = 0).
   From the loop head, sbd_emit_loop (SbDecSegB.v) walks both turns of the emit loop and the run to 0x83790.
   Its premise sbd_lh, which this file proves, carries the facts that decide the emit loop's error branches
   in each turn: s4 = i <= 1 and s10 = ~(F + 32) >= 2^64 - 2^47, so the pointer-overflow trap bltu s10,s4 at
   0x83754 is never taken; the shadow byte of the digit slot is 04 and F + 32 is 8-aligned, so in the shadow
   check 0x83758..0x83788 the byte is non-zero and (F + 32 + i) & 7 = i < 4 takes blt a2,a1 at 0x83788 to
   0x8376c: the ASan load-report call at 0x8378c, which would fall through into 0x83790, is never reached. *)
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
(* segment B's statements, its symbolic states and its lemmas (sbd_entry, sbd_emit_loop, ...) *)
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
(* SbDecSegB.v's run side-condition tactics (sbd_wrange, sbd_frame_pos, sbd_awr, sbd_wr_slot, sbd_wr_img,
   sbd_pres_win, sbd_kvs) are local to its sections, so they are restated here under this file's prefix,
   with the same bodies. *)
Local Ltac sbd_v10a_wrange Ha :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  destruct Ha as (r & Hr & Ha); vm_compute in Hr;
  destruct Hr as [Hr | [Hr | Hr]]; [ | | exfalso; exact Hr ];
  subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Ha end.
Local Ltac sbd_v10a_frame_pos fp :=
  exists 0, fp;
  split; first [ left; reflexivity
               | left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia ].
(* the run writes only sb_dec's own frame *)
Local Ltac sbd_v10a_awr fp :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_v10a_wrange Ha; right; right; right; sbd_v10a_frame_pos fp.
(* the run's write window is the digit slot [F + 32, F + 36) *)
Local Ltac sbd_v10a_wr_slot :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; sbd_v10a_wrange Ha; lia.
(* the digit slot is in sb_dec's frame, which is not part of the image *)
Local Ltac sbd_v10a_wr_img Hfi0 :=
  let a := fresh "a" in let Hi := fresh "Hi" in let Ha := fresh "Ha" in
  let Hi2 := fresh "Hi2" in let Hfi := fresh "Hfi" in
  intros a Hi Ha; pose proof (pa_img_range a Hi) as Hi2; pose proof Hfi0 as Hfi;
  change (fs_frame_bytes 0) with 64 in Hfi; sbd_v10a_wrange Ha; lia.
(* the stack window of sb_dec is present in every state of its journal *)
Local Ltac sbd_v10a_pres_win HJx :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _);
  apply Hpr; lia.
(* a byte outside the digit slot is the same before and after the run *)
Local Ltac sbd_v10a_kvs HFr :=
  lazymatch type of HFr with
  | frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in let Hw := fresh "Hw" in
    intros a Ha Hn; apply (sbd_aview_frame _ m0 m1 (in_wrange E0 rs) a Ha);
    [ intros Hw; sbd_v10a_wrange Hw; apply Hn; clear - Hw; lia | exact HFr ]
  end.
Theorem sbd_segB_v10a : sbd_segB_v10a_spec B.
Proof.
unfold sbd_segB_v10a_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 Q
  Hv100 HAT HQ.
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
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* Two digits: 10 <= v (the loop's exit test at 0x8372c is not taken on the first turn) and v / 10 < 10 (it
   is taken on the second); both are conditions of the entry state. *)
assert (Hq10 : v / 10 < 10) by (apply Z.div_lt_upper_bound; lia).
assert (Hq31 : 0 <= v / 10 < 2 ^ 31) by (pose proof (sbd_div10_range v ltac:(lia)); lia).
assert (HC : conds_ok (sbd_env regs1 v (frame_addr lyc 0 fpos)) [sbd_ge 21; sbd_lt 32]).
{ split; [|split; [|exact I]].
  - apply (sbd_cond_ge _ 21 v ltac:(lia)); [| lia].
    unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl). exact R21.
  - refine (sbd_cond_lt _ 32 (v / 10) Hq31 _ Hq10).
    unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra regs1 _ 0). }
destruct (sbd_entry B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2
  s1v regs1 mem1 md1 [sbd_ge 21; sbd_lt 32] HAT HC) as [HS SHOK].
(* the atoms the side conditions and the loop head's registers speak about *)
assert (U25 : bv_unsigned (ew (sbd_env regs1 v (frame_addr lyc 0 fpos)) 25) = frame_addr lyc 0 fpos + 32).
{ unfold sbd_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl), R25. apply unsigned_lit_small. lia. }
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
(* the shadow byte of the digit slot lies outside the slot, and the frame inside the address space *)
assert (HSHNS : 0 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < 2 ^ 64 /\
  ~ (frame_addr lyc 0 fpos + 32 <= SHADOW_OFF + frame_addr lyc 0 fpos / 8 + 4 < frame_addr lyc 0 fpos + 36)).
{ pose proof (Z.div_mod (frame_addr lyc 0 fpos) 8 ltac:(lia)) as DF8.
  pose proof (Z.mod_pos_bound (frame_addr lyc 0 fpos) 8 ltac:(lia)) as MF8.
  unfold SHADOW_OFF. lia. }
assert (HFR : forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; lia).
(* the digits of this path: the model's sb_dec_D, two digits and no pad (2 >= md) *)
assert (Hlsd : sb_dec_c.sb_dec_lsd v 3 = [48 + v mod 10; 48 + v / 10 mod 10]).
{ cbn [sb_dec_c.sb_dec_lsd]. replace (v <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (v / 10 <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
assert (HDl : sb_dec_c.sb_dec_D v md = [48 + v / 10 mod 10; 48 + v mod 10]).
{ unfold sb_dec_c.sb_dec_D. rewrite Hlsd. cbn [length]. change (Z.of_nat 2) with 2.
  replace (2 <? md) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
remember (sbd_env regs1 v (frame_addr lyc 0 fpos)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sbd_env; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + 0x2f80)) with (Z_to_bv 64 (BASE + 0x2f80)).
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (BASE + 0x2f80)) mem1 (seg_rom SEGS))) in HJ.
(* the run from 0x836f4: both turns of the digit loop, the pad's branch at 0x83734 (taken: 2 >= md) and
   s4 := 1, s5 := -1, to the emit loop's head 0x83754 (BASE + 0x2fe0) *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2fe0; [sbd_v10a_awr fpos | ].
rename ms into ms2. rename HFr into HFr2. rename HG into HG2. clear HF.
assert (K : tcj_kept B SB_CH_STK lyc Sc W mem1 W (ms_mem ms2) s1v
  (fun a => frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36)).
{ eapply (sbd_kept_of_run B LAWS W _ _ mem1 (ms_mem ms2) lyc Sc S2 _ _ s1v SB_CH_STK);
  [ exact (proj1 HJ) | exact Habl | (intros cid0 pos0 Hin0; rewrite Hfrs; right; exact Hin0)
  | exact HFr2 | exact HG2 | sbd_v10a_wr_slot
  | sbd_v10a_wr_img (frm_off_imgP B lyc S2 W mem1 md1 0 fpos HAR Hin) | sbd_v10a_pres_win HJ ]. }
assert (KF : forall a, 0 <= a < 2 ^ 64 ->
  ~ (frame_addr lyc 0 fpos + 32 <= a < frame_addr lyc 0 fpos + 36) ->
  aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem1 a) by sbd_v10a_kvs HFr2.
(* the two digits the loop left in the slot, read back from the symbolic state *)
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0.
destruct HR0 as (_ & _ & _ & HCH).
cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HCH.
rewrite U25 in HCH.
repeat (let Hk := fresh "HCk" in apply Forall_cons_iff in HCH; destruct HCH as [Hk HCH]).
repeat match goal with
| H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff 35 48))) |- _ =>
    let Hd := fresh "HDG" in
    pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SOff 35 48) (48 + v mod 10) H
      ltac:(cbn [sv_denot]; rewrite U35; f_equal; apply Z.add_comm)
      ltac:(pose proof (Z.mod_pos_bound v 10 ltac:(lia)); lia)) as Hd; clear H
| H : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff 36 48))) |- _ =>
    let Hd := fresh "HDG" in
    pose proof (sbd_aview_chunk W (ms_mem ms2) E _ o (SOff 36 48) (48 + v / 10 mod 10) H
      ltac:(cbn [sv_denot]; rewrite U36; f_equal; apply Z.add_comm)
      ltac:(pose proof (Z.mod_pos_bound (v / 10) 10 ltac:(lia)); lia)) as Hd; clear H
end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Qg =>
  change (SRr SEGS W (cfg_at SEGS (BASE + 0x2fe0) rg mm mdx) Qg) end.
prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
prreg HS (8%bv : bv 5) P8; prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19;
prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22;
prreg HS (23%bv : bv 5) P23; prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25;
prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27.
(* the emit loop from its head, turn index 1, no digit emitted yet (sbd_emit_loop) *)
eapply (sbd_emit_loop B LAWS HSC PSIG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n
          ov fpos S2 s1v regs1 mem1 md1 Q HAT HQ 1%nat 0%nat n ov (ms_regs ms2) (ms_mem ms2) _).
unfold sbd_lh.
split; [lia|].
split; [rewrite HDl; reflexivity|].
split; [exact HJ|].
split; [rewrite P2, EE2; reflexivity|].
split; [rewrite P3, EE3; reflexivity|].
split; [rewrite P4, EE4; reflexivity|].
split; [rewrite P8, EE8; reflexivity|].
split; [rewrite P18, EE18; reflexivity|].
split; [rewrite P19, EE19; reflexivity|].
split; [rewrite P20; reflexivity|].
split; [rewrite P21; reflexivity|].
split; [rewrite P22, EE22; reflexivity|].
split; [rewrite P23, EE23; reflexivity|].
split; [rewrite P24, EE24; reflexivity|].
split; [rewrite P25, EE25; reflexivity|].
split; [rewrite P26, EE26; reflexivity|].
split; [rewrite P27, EE27; reflexivity|].
split;
  [ intros t Ht; rewrite HDl; destruct t as [|[|t]]; try (exfalso; clear - Ht; lia);
    cbn [nth Nat.add Nat.sub Z.of_nat Pos.of_succ_nat]; assumption | ].
split; [ intros a Ha Hn; exact (KF a (HFR a Ha) Hn) | ].
split; [ rewrite (KF _ (proj1 HSHNS) (proj2 HSHNS)); exact HSHB | ].
split;
  [ exact (sbd_inv0 B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v
             regs1 mem1 md1 (ms_mem ms2) _ HAT HJ K)
  | apply (sbd_kept_mono B _ _ _ _ _ _ _ _ _ K); intros a Ha; left; exact Ha ].
Qed.
End walk.
End h.
End f.
End d.
