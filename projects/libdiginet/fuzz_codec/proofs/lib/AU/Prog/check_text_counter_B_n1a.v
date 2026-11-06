(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 231 of its 263 lines of code are new or changed and 973 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_text_counter_B_s0a.v, with its module names changed; 164 of its 201 lines of code are new or changed and 226 lines of the source are left out. *)
(* Segment N1a of check_text_counter's walk in image B (check_text_counter_B_inv.v): from the entry of
   owed_counter_text 0x84474 (cc_cut .. B_OWED_CT) through its contract (cdcU_owed_counter_text_specX: the text q, the
   eight digits at want[8] = F + 32, an object of the walk's own frame, and the want dots byte s1 + 55 on the walk's
   machine stack) to its return 0x842dc, then s7 = its rc, a1 = 0xa5, a2 = 24, s2 = 0xa5, a0 = sg, jal __asan_memset
   at 0x842f0: to its entry 0x51f84 (cc_cut .. CC_CM). The callee writes want[8] and the dots byte (and its own window
   below sp1); the save area, the spill slot 24(s1), the flag word and the frame's shadow are kept by its post. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_mi check_text_scribble_B_m2.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv check_text_counter_B_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis OWED : cdcU_owed_counter_text_specX tfibsegs B MT CB_RLO CB_RHI GLYPHA ROSTRS B_OWED_CT.

Theorem cc_n1a_holds : cc_seg_N1a B MT SEG7TBL GLYPHA ROSTRS.
Proof.
unfold cc_seg_N1a. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R1 & R10 & R11 & R12 & R19 & Vdot).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R25 & R22 & R26 & R24 & R21 & R20 & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
pose proof Hpre as (HE & _ & Hstr & Hoq & Hosg & Hodt & _ & Hsg & _ & _ & _ & Hdt & _ & Hd1 & Hd2 & Hd3 & Himg & Hagr & Hfr6).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HE) as HJc. pose proof (proj1 HJc) as HARc.
destruct (cc_stack B SEG7TBL GLYPHA ROSTRS g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (cc_frame B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ)
  as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra & Hqhull) & _ & _).
assert (Hsp1m : cc_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (cc_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (cc_sp1 g / 32)) with ((2 * (cc_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Esp : spZ regs2 = cc_sp1 g) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hbl : forall b m, In (b, m) (ablocks B (cc_lyc g) (cc_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym HP) Hin)).
assert (Hfi : forall c p, In (c, p) (frames (cc_Sc g)) -> In (c, p) (frames S2))
  by (intros c p Hin; rewrite Hfr; right; exact Hin).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof Hstr as (Hq0 & _ & Hz0 & (_ & Hqn & _ & _ & _ & Hqam & Hqwin)).
assert (Hlen1 : 1 <= cc_len g) by (unfold cc_len; destruct (cc_tb g); [destruct Hz0 | cbn [length]; lia]).
assert (HqS : cc_q g + cc_len g <= cc_sp g - 8384 \/ cc_sp g <= cc_q g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hqwin; unfold cc_len; lia).
(* the bytes of want[8] are fresh, so the text is apart from them *)
assert (HqW : cc_q g + cc_len g <= cc_F g pos + 32 \/ cc_F g pos + 32 + 8 <= cc_q g).
{ destruct (cc_fresh_disj B (cc_lyc g) (cc_Sc g) (cc_q g) (cc_len g) (cc_F g pos + 32) 8 Hoq
    ltac:(intros a Ha; apply (cc_fresh B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP); left; lia)
    ltac:(lia) ltac:(lia)); lia. }
destruct (garr8_of_present tfibsegs (mrestrict (w_H W2) mem2) (cc_F g pos + 32) 8) as (sw0 & Hsw0l & Hsw0).
{ intros a Ha. destruct (HFp a ltac:(cbn in Ha; lia)) as (Hh & b & Hb). exists b. unfold mrestrict. rewrite Hh. exact Hb. }
eapply SRr_bind.
{ apply (OWED (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g) ((0, pos) :: cc_own g)
    ly2 S2 W2 mem2 md2 (cc_k g) regs2 (cc_q g) (cc_F g pos + 32) (cc_sp1 g + 55) (cc_tb g) sw0 0).
  - apply (cpw_entry B _ _ _ _ _ _ _ _ _ (cc_lyc g) (cc_Sc g)); [exact HJ | | | | | | | | exact Hev | exact HP | exact Hlive].
    + rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + rewrite Esp. exact Hsp1m.
    + rewrite Esp. unfold TB_owed_counter_text, ESTACK. lia.
    + rewrite Esp. lia.
  - exact R10.
  - split; [exact Hq0|]. split; [exact Htb|]. split; [exact Hz0|].
    split; [lia|]. split; [unfold cc_len in Hqn; exact Hqn|].
    split; [intros a Ha; destruct (Htb (Z.to_nat (a - cc_q g)) ltac:(unfold cc_len in Ha; lia)) as (Va & Ba);
            rewrite Z2Nat.id in Va by lia; replace (cc_q g + (a - cc_q g)) with a in Va by lia;
            rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba); discriminate|].
    split; [exact Htra|]. split; [intros _; exact Hqhull|]. split; [exact Hqam|].
    unfold coff_win. rewrite Esp. unfold TB_owed_counter_text, ESTACK. unfold cc_len in HqS. lia.
  - exact (cc_cobj_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_q g) (cc_len g) Hoq Hbl Hfi Efa).
  - right. exists 0, pos. split; [exact Hin|]. rewrite Efa. fold (cc_F g pos). change (fs_frame_bytes 0) with 64. lia.
  - exact R11.
  - rewrite Esp. apply (sat_c0_obj_dst tfibsegs B LAWS (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g)
      (cc_mem0 g) (cc_md0 g) ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g) (cc_sp1 g) TB_owed_counter_text pos
      (cc_F g pos) 8 HJ ltac:(left; reflexivity) Hin (Efa 0 pos) HF64 ltac:(lia) ltac:(lia)
      (cc_want_bs (w_H W2) mem2 (cc_F g pos) HF64 ltac:(lia) Hsh));
    unfold TB_owed_counter_text, ESTACK; lia.
  - exact Hsw0.
  - exact Hsw0l.
  - exact R12.
  - right. rewrite Esp. apply (sat_stack_dst tfibsegs B LAWS (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g)
      (cc_mem0 g) (cc_md0 g) ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g)); [exact HJ | lia | lia | lia | lia |].
    unfold TB_owed_counter_text, ESTACK. lia.
  - exact Vdot.
  - left. lia.
  - unfold cc_len in HqW. lia.
  - unfold cc_len in HqS. lia.
  - rewrite Esp. apply (cc_cimg_up B _ _ _ _ _ _ _ _ _ HK _ _ _ _ _ _ Himg);
      [unfold TB_owed_counter_text, TB_check_text_counter, ESTACK; lia | lia | intros r Hr; right; exact Hr].
  - rewrite Hfr. cbn [length]. lia. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & KT3 & HRc).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite Esp in KT3. unfold TB_owed_counter_text in KT3.
rewrite R1.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HP3.
(* the owed result *)
assert (HOW : owed_counter_text_spec (cc_tb g) = (cc_ro g, cc_so g, cc_do g))
  by (unfold cc_ro, cc_so, cc_do; destruct (owed_counter_text_spec (cc_tb g)) as [[x y] z]; reflexivity).
rewrite HOW in HRc. destruct HRc as (Ha0 & HR0 & HRn).
(* what the callee kept: the save area, the spill slot, the flag word and the frame's shadow *)
assert (KOFF : forall a, (cc_sp g - 104 <= a < cc_sp g) \/ (cc_F g pos + 56 <= a < cc_F g pos + 64) \/
    (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) \/ (cc_sp1 g + 24 <= a < cc_sp1 g + 32) ->
    aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ assert (HF8 : 0 <= cc_F g pos / 8 /\ 8 * (cc_F g pos / 8) <= cc_F g pos)
    by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  eapply (cc_koff_cj B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 W3 mem3);
    [exact Hpre | exact HJ | exact KT3 | unfold ESTACK; lia |].
  intros a Ha Hx. cbv beta in Ha. unfold SB in *. lia. }
(* the walk's kept invariant through the call: the callee wrote want[8] (fresh) and the dots byte (the window) *)
assert (KTc : tcj_kept tfibsegs B TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) W3 mem3 (cc_sp g)
  (cc_wr g)).
{ eapply (cw_kept_cj B LAWS) with (1 := HJc) (2 := HJ) (4 := HP) (10 := HK) (11 := KT3);
  [ rewrite Hfr; apply incl_tl, incl_refl | unfold TB_check_text_counter, ESTACK; lia | lia
  | unfold TB_check_text_counter, ESTACK; lia | lia
  | intros a Ha; cbv beta in Ha; destruct Ha as [Ha | Ha];
    [ right; right; apply (cc_fresh B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP); left; lia
    | left; unfold TB_check_text_counter, ESTACK; lia ] ]. }
(* the state at 0x842dc *)
set (E := Ereg regs3 (cw_extra [])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs3 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (HS : st_ok tfibsegs E (mkSS 0x842dc sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x842dc) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (EC : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> ew E nn = getr regs2 r).
{ intros nn r Hnn Hcs. rewrite (EE nn r Hnn). pose proof (CS _ Hcs) as Hc. rewrite Hnn, !Z_to_bv_bv_unsigned in Hc.
  exact Hc. }
assert (E10 : ew E 10 = w64 (cc_ro g)) by (rewrite (EE 10%nat 10%bv eq_refl); exact Ha0).
assert (E19 : ew E 19 = w64 (cc_sg g)) by (rewrite (EC 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R19).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros; assumption).
(* 0x842dc .. 0x842f0: s7 = rc, a1 = 0xa5, a2 = 24, s2 = 0xa5, a0 = sg, jal __asan_memset *)
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) CC_CM. ctk_keep cw_kwr_ro.
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md4] =>
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
  exists ly3, S3, (ms_regs msv), (ms_mem msv), md4;
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
end.
split; [exact HJ3|].
split.
{ apply (cw_kept_step B LAWS TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_mdc g) W3 mem3
    _ (cc_sp g) (cc_wr g) (fun _ => False));
  [ unfold TB_check_text_counter, ESTACK; lia | exact HARc | exact KTc | exact KE | intros a [] | exact KP ]. }
split; [exact (Permutation_trans HPerm3 HP)|].
split; [exact Hni|].
split; [eapply same_io_trans; [exact (same_io_trans _ _ _ Hio HIO3) | kio]|].
split; [pose proof (mle_station _ _ _ _ 0 0 MTL Hmo HMLE3) as HMOn; rewrite Z.add_0_r in HMOn; exact HMOn|].
assert (HF8g : 0 <= cc_F g pos / 8 /\ 8 * (cc_F g pos / 8) <= cc_F g pos)
  by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
split.
{ apply (cc_common_keep g pos regs2 mem2 W2 _ _ W3 HC);
  [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
  | intros a Ha; rewrite KE by (first [unfold SB in *; lia | tauto]); exact (KOFF a Ha) ]. }
split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|].
split; [bsm_rf|].
(* what owed_counter_text left at want[8] and the dots byte *)
destruct (Z.eq_dec (cc_ro g) 0) as [H0 | H0].
- destruct (HR0 H0) as (G & V). exists (cc_so g), (cc_do g).
  pose proof (cc_owed_len (cc_tb g) (cc_ro g) (cc_so g) (cc_do g) HOW H0) as Hlo.
  split; [apply (bs_garr8_kept (w_H W3) (w_H W3) mem3 _); [intros a Ha; rewrite Hlo in Ha; apply KE; [lia | tauto] | exact G]|].
  split; [exact Hlo|].
  split; [apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 _ _ 1 _); [intros a Ha; apply KE; [lia | tauto] | exact V]|].
  intros _. split; reflexivity.
- destruct (HRn H0) as (sw & v2 & G & L & V). exists sw, v2.
  split; [apply (bs_garr8_kept (w_H W3) (w_H W3) mem3 _); [intros a Ha; rewrite L in Ha; apply KE; [lia | tauto] | exact G]|].
  split; [exact L|].
  split; [apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 _ _ 1 _); [intros a Ha; apply KE; [lia | tauto] | exact V]|].
  intros Hc. contradiction.
Qed.
End s.
