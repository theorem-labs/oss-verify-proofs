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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_text_counter_B_n1a.v, with its module names and addresses changed; 272 of its 381 lines of code are new or changed and 92 lines of the source are left out. *)
(* Segment N2 of check_text_counter's walk in image B (check_text_counter_B_inv.v): from the entry of
   diginet_counter_text 0x869e4 (cc_cut .. B_COUNTER_TEXT) through its contract (cdcU_counter_text_specX: the text q,
   the record's first 8 bytes, which hold 0xa5, and dt, which holds 0xa5) to its return 0x84318, then
   0x84318 bne a0,s7: not taken, the library's result is the owed one (the contract's premise on the two texts);
   0x8431c bnez s7: a result other than 0 goes to 0x84348: the UBSan check of sg + 8 (0x8434c, not taken: sg is
   below 2 ^ 47), s3 = sg + 8, a1 = 0, a2 = 0xa5, a3 = ~(sg + 8), a4 = 16: to the fuzz_all loop's head 0x84364
   (cc_cut .. CC_FL); a result 0 goes to a2 = 8, a0 = sg, a1 = want, jal the compare wrapper at 0x8432c: to its entry
   0x42430 (cc_cut .. CC_CB). The callee writes the record's first 8 bytes, dt and its own window below sp1. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnLib DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_s0a check_text_scribble_B_s0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_mi.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_m2 check_text_scribble_B_m3.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv check_text_counter_B_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a sub-range of an object is an object *)
Lemma cc_cobj_sub : forall B ly S q n m, cobj_ok B ly S q n -> 0 <= m <= n -> cobj_ok B ly S q m.
Proof.
intros B ly S q n m [(b & mm & Hin & H1 & H2) | (c & p & Hin & H1 & H2)] Hm.
- left. exists b, mm. split; [exact Hin | lia].
- right. exists c, p. split; [exact Hin | lia].
Qed.
(* the first k bytes of a list of 0xa5 *)
Lemma cc_garr8_rep_sub : forall segs (m : word -> option byte) a k n, (k <= n)%nat ->
  garr8 segs m a (repeat 165 n) -> garr8 segs m a (repeat 165 k).
Proof.
intros segs m a k n Hk Hg j Hj. rewrite repeat_length in Hj. rewrite (bsf_nth_repeat k j 165 0 Hj).
destruct (Hg j ltac:(rewrite repeat_length; lia)) as (V & Bd). rewrite (bsf_nth_repeat n j 165 0 ltac:(lia)) in V, Bd.
split; [exact V | exact Bd].
Qed.

(* the result code of the second loop of the two counter texts: 0 or E_RANGE *)
Lemma cc_ct2_rc : forall n s dot k i seg d,
  fst (fst (DgnLib.ct2_go n s dot i k seg d)) = 0 \/ fst (fst (DgnLib.ct2_go n s dot i k seg d)) = DgnSpec.E_RANGE.
Proof.
intros n s dot k. induction k as [|k IH]; intros i seg d; cbn [DgnLib.ct2_go]; [left; reflexivity|].
destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0)); [destruct (i =? 7)|];
  first [right; reflexivity | apply IH].
Qed.
Lemma cc_owed_rc : forall tb, fst (fst (owed_counter_text_spec tb)) = 0 \/ fst (fst (owed_counter_text_spec tb)) = DgnSpec.E_RANGE.
Proof.
intros tb. unfold owed_counter_text_spec. destruct (ct1_owe tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- unfold DgnLib.ct2. apply cc_ct2_rc.
- right; reflexivity.
Qed.
(* bnez on an atom holding a small signed value *)
Lemma cc_c_ne0 : forall Ev k x, ew Ev k = Z_to_bv 64 x -> - 2 ^ 63 <= x < 2 ^ 63 ->
  branch_taken BC_NE (sv_denot Ev (SOff k 0)) (sv_denot Ev (SLit 0)) = negb (x =? 0).
Proof.
intros Ev k x Hk Hx. rewrite branch_ne_U, U_SOff, U_lit by lia. rewrite Hk, Z.add_0_r, Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod.
destruct (Z.eqb_spec x 0) as [-> | Hx0]; [reflexivity|].
replace (x mod 2 ^ 64 =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intros H0.
destruct (Z_lt_le_dec x 0) as [Hn | Hp].
- rewrite <- (Z.mod_add x 1 (2 ^ 64)) in H0 by lia. rewrite Z.mod_small in H0 by lia. lia.
- rewrite Z.mod_small in H0 by lia. lia.
Qed.

(* the record: eight digits in front of the sixteen 0xa5 bytes *)
Lemma cc_rep_shift : forall segs (m : word -> option byte) sg,
  garr8 segs m sg (repeat 165 24) -> garr8 segs m (sg + 8) (repeat 165 16).
Proof.
intros segs m sg Hr j Hj. rewrite repeat_length in Hj. rewrite (bsf_nth_repeat 16 j 165 0 Hj).
destruct (Hr (j + 8)%nat ltac:(rewrite repeat_length; lia)) as (V & Bd).
rewrite (bsf_nth_repeat 24 (j + 8) 165 0 ltac:(lia)) in V, Bd.
replace (sg + 8 + Z.of_nat j) with (sg + Z.of_nat (j + 8)) by lia. split; [exact V | exact Bd].
Qed.
Lemma cc_rec_join : forall segs (m : word -> option byte) sg (s : list Z), length s = 8%nat ->
  garr8 segs m sg s -> garr8 segs m (sg + 8) (repeat 165 16) -> garr8 segs m sg (s ++ repeat 165 16).
Proof.
intros segs m sg s Hl Hs Hr j Hj. rewrite length_app, repeat_length, Hl in Hj.
destruct (Nat.lt_ge_cases j 8) as [H8 | H8].
- rewrite app_nth1 by lia. exact (Hs j ltac:(lia)).
- rewrite app_nth2 by lia. rewrite Hl. destruct (Hr (j - 8)%nat ltac:(rewrite repeat_length; lia)) as (V & Bd).
  replace (sg + 8 + Z.of_nat (j - 8)) with (sg + Z.of_nat j) in V by lia. split; [exact V | exact Bd].
Qed.

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
Hypothesis CTX : cdcU_counter_text_specX tfibsegs B MT CB_RLO CB_RHI SEG7TBL B_COUNTER_TEXT.

Theorem cc_n2_holds : cc_seg_N2 B MT SEG7TBL GLYPHA ROSTRS.
Proof.
unfold cc_seg_N2. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R1 & R10 & R11 & R12 & R19 & R23 & R27 & Hrec & Hdt165 & Howres).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R25 & R22 & R26 & R24 & R21 & R20 & _).
pose proof Hpre as (HE & _ & Hstr & Hoq & Hosg & Hodt & _ & (Hsg0 & Hsgn & Hsgtd & Hsgtw & _ & _ & Hsgam & Hsgwin) & _ & _ & _ &
  (Hdt0 & Hdtn & Hdttd & Hdttw & _ & _ & Hdtam & Hdtwin) & _ & Hd1 & Hd2 & Hd3 & Himg & Hagr & Hfr6).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HE) as HJc. pose proof (proj1 HJc) as HARc.
destruct (cc_stack B SEG7TBL GLYPHA ROSTRS g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (cc_frame B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ)
  as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra & Hqhull) & (Hsgra & Hsghull) & (Hdtra & Hdthull)).
assert (Hsp1m : cc_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (cc_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (cc_sp1 g / 32)) with ((2 * (cc_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Esp : spZ regs2 = cc_sp1 g) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hbl : forall b m, In (b, m) (ablocks B (cc_lyc g) (cc_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym HP) Hin)).
assert (Hfi : forall c p, In (c, p) (frames (cc_Sc g)) -> In (c, p) (frames S2))
  by (intros c p Hin; rewrite Hfr; right; exact Hin).
pose proof Hstr as (Hq0 & _ & Hz0 & (_ & Hqn & _ & _ & _ & Hqam & Hqwin)).
assert (Hlen1 : 1 <= cc_len g) by (unfold cc_len; destruct (cc_tb g); [destruct Hz0 | cbn [length]; lia]).
assert (HqS : cc_q g + cc_len g <= cc_sp g - 8384 \/ cc_sp g <= cc_q g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hqwin; unfold cc_len; lia).
assert (HsgS : cc_sg g + 24 <= cc_sp g - 8384 \/ cc_sp g <= cc_sg g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hsgwin; lia).
assert (HdtS : cc_dt g + 1 <= cc_sp g - 8384 \/ cc_sp g <= cc_dt g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hdtwin; lia).
eapply SRr_bind.
{ apply (CTX (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g) ((0, pos) :: cc_own g)
    ly2 S2 W2 mem2 md2 (cc_k g) regs2 (cc_q g) (cc_sg g) (cc_dt g) (cc_tb g) (repeat 165 8) 165).
  - apply (cpw_entry B _ _ _ _ _ _ _ _ _ (cc_lyc g) (cc_Sc g)); [exact HJ | | | | | | | | exact Hev | exact HP | exact Hlive].
    + rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + rewrite Esp. exact Hsp1m.
    + rewrite Esp. unfold TB_counter_text, ESTACK. lia.
    + rewrite Esp. lia.
  - exact R10.
  - split; [exact Hq0|]. split; [exact Htb|]. split; [exact Hz0|].
    split; [lia|]. split; [unfold cc_len in Hqn; exact Hqn|].
    split; [intros a Ha; destruct (Htb (Z.to_nat (a - cc_q g)) ltac:(unfold cc_len in Ha; lia)) as (Va & Ba);
            rewrite Z2Nat.id in Va by lia; replace (cc_q g + (a - cc_q g)) with a in Va by lia;
            rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba); discriminate|].
    split; [exact Htra|]. split; [intros _; exact Hqhull|]. split; [exact Hqam|].
    unfold coff_win. rewrite Esp. unfold TB_counter_text, ESTACK. unfold cc_len in HqS. lia.
  - exact (cc_cobj_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_q g) (cc_len g) Hoq Hbl Hfi Efa).
  - exact (cc_cobj_sub B ly2 S2 (cc_sg g) 24 8 (cc_cobj_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_sg g) 24 Hosg Hbl Hfi Efa)
      ltac:(lia)).
  - exact (cc_cobj_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_dt g) 1 Hodt Hbl Hfi Efa).
  - exact R11.
  - split; [lia|]. split; [lia|].
    split; [apply (bsm_tdst_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_sg g) 8); [| exact Hbl | exact Hfi | exact Efa];
            intros a Ha; apply Hsgtd; lia|].
    split.
    { intros a Ha. destruct (Hsgtw a ltac:(lia)) as (Haw & _ & _ & _).
      split; [apply (bsm_awr_mono _ _ _ _ _ _ _ _ _ _ _ Haw); [exact Hbl | apply incl_tl, incl_refl | exact Efa]|].
      split; [apply (bsm_tdst_present B LAWS ly2 S2 W2 mem2 md2 (cc_sg g) 24 a HAR2);
              [apply (bsm_tdst_mono B (cc_lyc g) (cc_Sc g)); [exact Hsgtd | exact Hbl | exact Hfi | exact Efa] | lia]|].
      split; [|rewrite Esp; unfold ESTACK; lia].
      exact (bsm_tdst_not_owned B LAWS ly2 S2 W2 mem2 md2 (cc_sg g) 24 a HAR2
        (bsm_tdst_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_sg g) 24 Hsgtd Hbl Hfi Efa) ltac:(lia)). }
    split; [intros x Hx; apply Hsgra; lia|].
    split; [intros Hn0; exact (bsm_hull_sub _ (cc_sg g) 8 24 ltac:(lia) ltac:(lia) Hsghull)|].
    split; [unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia|].
    unfold coff_win. rewrite Esp. unfold TB_counter_text, ESTACK. lia.
  - exact (cc_garr8_rep_sub tfibsegs _ (cc_sg g) 8 24 ltac:(lia) Hrec).
  - reflexivity.
  - exact R12.
  - split; [lia|]. split; [lia|].
    split; [apply (bsm_tdst_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_dt g) 1); [exact Hdttd | exact Hbl | exact Hfi | exact Efa]|].
    split.
    { intros a Ha. destruct (Hdttw a Ha) as (Haw & _ & _ & _).
      split; [apply (bsm_awr_mono _ _ _ _ _ _ _ _ _ _ _ Haw); [exact Hbl | apply incl_tl, incl_refl | exact Efa]|].
      split; [apply (bsm_tdst_present B LAWS ly2 S2 W2 mem2 md2 (cc_dt g) 1 a HAR2);
              [apply (bsm_tdst_mono B (cc_lyc g) (cc_Sc g)); [exact Hdttd | exact Hbl | exact Hfi | exact Efa] | lia]|].
      split; [|rewrite Esp; unfold ESTACK; lia].
      exact (bsm_tdst_not_owned B LAWS ly2 S2 W2 mem2 md2 (cc_dt g) 1 a HAR2
        (bsm_tdst_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_dt g) 1 Hdttd Hbl Hfi Efa) ltac:(lia)). }
    split; [exact Hdtra|].
    split; [intros _; exact Hdthull|].
    split; [unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia|].
    unfold coff_win. rewrite Esp. unfold TB_counter_text, ESTACK. lia.
  - exact Hdt165.
  - lia.
  - unfold cc_len in Hd2. lia.
  - unfold cc_len in Hd3. lia.
  - rewrite Esp. apply (cc_cimg_up B _ _ _ _ _ _ _ _ _ HK _ _ _ _ _ _ Himg);
      [unfold TB_counter_text, TB_check_text_counter, ESTACK; lia | lia | intros r [Hr | []]; left; exact Hr].
  - rewrite Hfr. cbn [length]. lia. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & KT3 & HRES).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite Esp in KT3. unfold TB_counter_text in KT3.
rewrite R1.
clear Hd2 Hd3 HqS Hqwin.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HP3.
assert (HOW : owed_counter_text_spec (cc_tb g) = (cc_ro g, cc_so g, cc_do g))
  by (unfold cc_ro, cc_so, cc_do; destruct (owed_counter_text_spec (cc_tb g)) as [[x y] z]; reflexivity).
rewrite HOW in Hagr.
destruct (DgnLib.counter_text_spec (cc_tb g)) as [[rl sl] dl] eqn:HCL.
cbv beta iota in Hagr, HRES.
destruct Hagr as (Hr12 & Hr0). destruct HRES as (Ha0 & HR0 & HRn).
(* the state at 0x84318 *)
set (E := Ereg regs3 (cw_extra [])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs3 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (HS : st_ok tfibsegs E (mkSS 0x84318 sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x84318) mem3 (seg_rom tfibsegs)))).
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
assert (E10 : ew E 10 = w64 (cc_ro g)) by (rewrite (EE 10%nat 10%bv eq_refl), Ha0, Hr12; reflexivity).
assert (E23 : ew E 23 = w64 (cc_ro g)) by (rewrite (EC 23%nat 23%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R23).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros; assumption).
(* 0x84318 bne a0,s7: not taken *)
cw_branch Hc.
{ exfalso. rewrite branch_ne_U, !U_SOff in Hc. ewpeel_in Hc. rewrite E10, E23, Z.eqb_refl in Hc. discriminate Hc. }
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) CC_CB. ctk_keep cw_kwr_ro.
assert (Hro : cc_ro g = 0 \/ cc_ro g = DgnSpec.E_RANGE) by (unfold cc_ro; apply cc_owed_rc).
unfold DgnSpec.E_RANGE in Hro.
assert (E19 : ew E 19 = w64 (cc_sg g)) by (rewrite (EC 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R19).
assert (E22 : ew E 22 = w64 (cc_F g pos + 32))
  by (rewrite (EC 22%nat 22%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R22).
assert (E27 : ew E 27 = w64 (SB + cc_dt g / 8))
  by (rewrite (EC 27%nat 27%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R27).
(* the bytes the walk reads after the call: the record's bytes [8, 24), want, the want dots byte, dt *)
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (HFF : forall a, cc_F g pos <= a < cc_F g pos + 64 -> cw_fresh B (cc_lyc g) (cc_Sc g) a)
  by (intros a Ha; exact (cc_fresh B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP (or_introl Ha))).
assert (KW : forall a, cc_F g pos <= a < cc_F g pos + 64 \/ cc_sp1 g + 24 <= a < cc_sp1 g + 64 ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. pose proof KT3 as (K1 & _ & _ & K4 & _).
  assert (HnE : ~ (cc_sg g <= a < cc_sg g + 8 \/ cc_dt g <= a < cc_dt g + 1)).
  { intros [Hr | Hr]; destruct Ha as [Ha | Ha].
    - exact (cc_obj_not_fresh B _ _ _ _ a Hosg ltac:(lia) (HFF a Ha)).
    - lia.
    - exact (cc_obj_not_fresh B _ _ _ _ a Hodt ltac:(lia) (HFF a Ha)).
    - lia. }
  destruct Ha as [Ha | Ha].
  - apply (K4 0 pos a Hin); [left | exact HnE].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes 0) with 64. fold (cc_F g pos). lia.
  - apply K1; [lia | lia | exact HnE]. }
assert (KREC : forall x, cc_sg g + 8 <= x < cc_sg g + 24 ->
  aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply (bsm_obj_kept_cj B TB_counter_text (cc_lyc g) (cc_Sc g) ly2 S2 W2 mem2 W3 mem3 (cc_sp1 g)
    (fun x0 => cc_sg g <= x0 < cc_sg g + 8 \/ cc_dt g <= x0 < cc_dt g + 1) (cc_sg g) 24 KT3 Hsgtd Hbl Hfi Efa x
    ltac:(lia)).
  cbv beta. lia. }
assert (HF8 : 0 <= cc_F g pos / 8 /\ 8 * (cc_F g pos / 8) <= cc_F g pos)
  by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
assert (Hsgapp : forall a, cc_sg g <= a < cc_sg g + 24 -> 4096 <= a < alloc_ceiling /\
  (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a))
  by (intros a Ha; exact (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HARc Hsgtd Ha)).
assert (Hdtapp : 4096 <= cc_dt g < alloc_ceiling /\ (cc_dt g + 1 <= kLowShadowBeg \/ kHighMemBeg <= cc_dt g))
  by (exact (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ (cc_dt g) HARc Hdttd ltac:(lia))).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* what the callee kept: the save area, the flag word, the frame's shadow and the spill slot *)
assert (KOFF : forall a, (cc_sp g - 104 <= a < cc_sp g) \/ (cc_F g pos + 56 <= a < cc_F g pos + 64) \/
    (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) \/ (cc_sp1 g + 24 <= a < cc_sp1 g + 32) ->
    aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ eapply (cc_koff_cj B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 W3 mem3);
    [exact Hpre | exact HJ | exact KT3 | unfold ESTACK; lia |].
  intros a Ha Hz. cbv beta in Ha. destruct Ha as [Ha | Ha].
  - destruct (Hsgapp a ltac:(lia)) as (_ & Hap).
    destruct Hz as [Hz | [Hz | [Hz | Hz]]];
    [ lia | exact (cc_obj_not_fresh B _ _ _ _ a Hosg ltac:(lia) (HFF a ltac:(lia)))
    | unfold SB, kLowShadowBeg, kHighMemBeg in *; lia | lia ].
  - destruct Hz as [Hz | [Hz | [Hz | Hz]]];
    [ lia | exact (cc_obj_not_fresh B _ _ _ _ a Hodt ltac:(lia) (HFF a ltac:(lia)))
    | unfold SB, kLowShadowBeg, kHighMemBeg in *; lia | lia ]. }
(* the walk's kept invariant through the call *)
assert (KTc : tcj_kept tfibsegs B TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) W3 mem3 (cc_sp g)
  (cc_wr g)).
{ eapply (cw_kept_cj B LAWS) with (1 := HJc) (2 := HJ) (4 := HP) (10 := HK) (11 := KT3);
  [ rewrite Hfr; apply incl_tl, incl_refl | unfold TB_check_text_counter, ESTACK; lia | lia
  | unfold TB_check_text_counter, ESTACK; lia | lia
  | intros a Ha; cbv beta in Ha; right; left; split;
    [ unfold cc_wr; lia
    | intros Him; destruct Ha as [Ha | Ha];
      [ exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ a HARc Hsgtd ltac:(lia) Him)
      | exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ a HARc Hdttd ltac:(lia) Him) ] ] ]. }
clear Hd1 HsgS HdtS HFapp Hdtapp Hsgwin Hdtwin.
cw_branch Hc2.
all: rewrite (cc_c_ne0 E 23 (cc_ro g) E23 ltac:(destruct Hro; lia)) in Hc2.
all: clear Hro.
- (* a result other than 0: to the fuzz_all loop *)
  apply negb_true_iff, Z.eqb_neq in Hc2.
  cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) CC_FL. ctk_keep cw_kwr_ro.
  cw_branch Hc3.
  { exfalso. rewrite branch_geu_U in Hc3.
    lazymatch type of Hc3 with context [U ?Ev (SOff 19 0)] =>
      rewrite (U_atom Ev 19 (cc_sg g) ltac:(ewpeel; exact E19) ltac:(lia)), U_SLit in Hc3 end.
    apply negb_true_iff, Z.ltb_ge in Hc3. rewrite zcanon_id in Hc3 by (unfold M64; lia).
    destruct (Hsgapp (cc_sg g) ltac:(lia)) as ((_ & Hlt) & _). lia. }
  cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) CC_FL. ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. right.
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
  split.
  { apply (cc_common_keep g pos regs2 mem2 W2 _ _ W3 HC);
    [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
    | intros a Ha; rewrite KE by (first [unfold SB in *; lia | tauto]); exact (KOFF a Ha) ]. }
  exists 0.
  split; [bsm_rf|].
  split; [bsm_rv0; rewrite denot_lit_U;
          lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
            rewrite (U_atom_off Ev 19 (cc_sg g) 8 ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia)) end; reflexivity|].
  split; [bsm_rf|].
  split; [bsm_rv0; lazymatch goal with |- sv_denot ?Ev _ = _ =>
            exact (bs_den_not Ev 19 (cc_sg g) 8 ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia)) end|].
  split; [bsm_rf|].
  split; [lia|]. split; [cbn; lia|].
  destruct (HRn ltac:(rewrite Hr12; exact Hc2)) as (s' & d' & Gs & Ls & Vd).
  exists s', d'. split; [exact Ls|]. split.
  + apply cc_rec_join; [exact Ls | |].
    * apply (bs_garr8_kept (w_H W3) (w_H W3) mem3 _); [|exact Gs].
      intros x Hx. rewrite Ls in Hx. apply KE; [lia | tauto].
    * apply (bs_garr8_kept (w_H W2) (w_H W3) mem2 _); [|exact (cc_rep_shift tfibsegs _ (cc_sg g) Hrec)].
      intros x Hx. rewrite repeat_length in Hx. rewrite KE by (first [lia | tauto]). apply KREC. lia.
  + apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 _ _ 1 _); [|exact Vd]. intros x Hx. apply KE; [lia | tauto].
- (* the result 0: to the compare wrapper *)
  apply negb_false_iff, Z.eqb_eq in Hc2.
  assert (Hrl0 : rl = 0) by lia.
  destruct (Hr0 Hrl0) as (Esl & Edl). destruct (HR0 Hrl0) as (Gs & Vd).
  pose proof (cc_lib_len (cc_tb g) rl sl dl HCL Hrl0) as Ls.
  destruct Howres as (sw & v2 & Gw & Lw & Vw & Hw). destruct (Hw Hc2) as (-> & ->).
  cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) CC_CB. ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. left.
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
  split.
  { apply (cc_common_keep g pos regs2 mem2 W2 _ _ W3 HC);
    [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
    | intros a Ha; rewrite KE by (first [unfold SB in *; lia | tauto]); exact (KOFF a Ha) ]. }
  split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|].
  exists sl, dl. split; [exact Ls|]. split; [|split; [|split]].
  + apply cc_rec_join; [exact Ls | |].
    * apply (bs_garr8_kept (w_H W3) (w_H W3) mem3 _); [|exact Gs].
      intros x Hx. rewrite Ls in Hx. apply KE; [lia | tauto].
    * apply (bs_garr8_kept (w_H W2) (w_H W3) mem2 _); [|exact (cc_rep_shift tfibsegs _ (cc_sg g) Hrec)].
      intros x Hx. rewrite repeat_length in Hx. rewrite KE by (first [lia | tauto]). apply KREC. lia.
  + rewrite Esl. apply (bs_garr8_kept (w_H W2) (w_H W3) mem2 _); [|exact Gw].
    intros x Hx. rewrite Lw in Hx. rewrite KE by (first [lia | tauto]). apply KW. left. lia.
  + apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 _ _ 1 _); [|exact Vd]. intros x Hx. apply KE; [lia | tauto].
  + rewrite Edl. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 _ _ 1 _); [|exact Vw].
    intros x Hx. cbn in Hx. rewrite KE by (first [lia | tauto]). apply KW. right. lia.
Qed.
End s.
