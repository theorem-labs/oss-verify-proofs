(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v; 145 of its 201 lines of code are new or changed and 905 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Dig.v at 97ea9c9eafa; for reac-pw/fuzz_headamp image A: module paths, the rs_ / rl_ / rm_ / RS_ / RM_ prefixes renamed to hs_ / hd_ / hm_ / HS_ / HM_; the real frame's cell R+0xf8 -> R+0x118; F's object window [F+0x20, F+0x158); the real frame of 0x1e0 bytes; the frame for locals of class 4 (1024 bytes, 128 shadow bytes); hs_pre at the start pattern and hd_seg_pre's conjunct order (R mod 32, pp's block from hd_fresh_block); hm_sh's sixth scope flag (x) out of scope. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): lib/A/HPgEnt0Def.v r7_dig_stmt, the DIG block of
   ent_build's case 0 (pod.h:237-246: the decimal text of c mod 64 into ch with its NUL, through r[4]), from the cut
   r7_cut_DIG at 0x81920 to the cut HPgSeg.hs_cut_G at G = 0x81a34. Proves no function (kind: segment lemma).

   HOW. lib/A/HPgEnt0DigW.v dg_walk walks the block over the journal (r into scope, the digits and the reverse into
   ch, r out of scope again). This file builds hs_cut_G from dg_walk's post: the journal-and-frame part (the cut's
   layout and state unchanged; the walk writes only ch, r and r's shadow byte, which lie in the frame's objects and
   its shadow row of HPgImgA hi_w1), the (location, value) facts (every register but a0 .. a7 and every real-frame
   cell kept), the frame's shadow (r's byte back to 0xf8, so the row is hs_PG again), the first block and e
   unchanged, ch holding dec64 (c mod 64) and its NUL, and the model's text by HPgEnt0Def.r7_g_of_cp. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgEnt0Def HPgW7bBase HPgEnt0Odd HPgEnt0DigW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* a register the walk keeps: x1 .. x9 and x18 .. x31 are outside dg_clob *)
Lemma dga_kept : forall (regs regs' : bvmap 5 word),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r dg_clob -> getr regs' r = getr regs r) ->
forall q, (1 <= q <= 9 \/ 18 <= q <= 31) -> getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q).
Proof.
intros regs regs' Hk q Hq.
assert (Hu : bv_unsigned (Z_to_bv 5 q) = q).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
apply Hk.
- rewrite Hu. lia.
- intros Hin. unfold dg_clob in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal (@bv_unsigned 5)) in Hin; rewrite Hu in Hin;
    vm_compute in Hin; lia|]).
  exact Hin.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an application byte is not a byte of the frame's shadow row *)
Lemma dga_not_shr : forall lo len a F, in_app lo len -> lo <= a < lo + len -> 4096 <= F -> F + 1024 <= DG_FHI ->
~ (shadow_addr F <= a < shadow_addr F + 128).
Proof.
intros lo len a F Happ Ha HF0 HF1 X. pose proof (dg_sh_bounds F HF0 HF1) as (SB0 & SB1).
revert SB0 SB1 Happ Ha X. unfold SHADOW_OFF. generalize (shadow_addr F). intros s SB0 SB1 Happ Ha X.
change (2 ^ 44) with 17592186044416 in SB1. zlia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.

Lemma r7_dig : r7_dig_stmt rsegs B MT.
Proof using LAWS.
unfold r7_dig_stmt, r7_from_DIG.
intros cx POST rest i k Hst HG ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb Hli Hlk Hcut.
destruct Hcut as (Hbase & Hat & Hfsh & Hpp & Hz & Hkd & Hcp & Hc & Hpb).
pose proof Hbase as (Hcore & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hes32 & _).
pose proof Hcore as (HJ2 & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof Hst as (Hpre & _ & _ & _).
pose proof Hpre as (HJc & _ & H2 & H3 & H4 & HeS & HR32 & HRS & HRSTK & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & Hppin & _)).
assert (HR16 : e_R (x_e cx) mod 16 = 0).
{ pose proof (Z.div_mod (e_R (x_e cx)) 32 ltac:(lia)) as D. rewrite HR32, Z.add_0_r in D. rewrite D.
  replace (32 * (e_R (x_e cx) / 32)) with ((2 * (e_R (x_e cx) / 32)) * 16) by ring. apply Z_mod_mult. }
cbn [hi_rsz hi_cid headamp_himg_A] in HRS, Hown, HF.
(* the bounds of R, F and pp *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= e_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : e_R (x_e cx) + 0x1e0 <= 2 ^ 47) by lia.
assert (HFa : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
assert (Hin3 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr, Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin3) as (HF32 & HFapp & _ & _).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin3) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, HFapp, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFapp, HFceil.
assert (HFhi : e_F (x_e cx) + 1024 <= DG_FHI) by (unfold DG_FHI; lia).
pose proof (dg_sh_bounds _ HF4096 HFhi) as (SB0 & SB1).
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & Hppapp & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos cx) HAR2 Hpp2 Hin3) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
set (F := e_F (x_e cx)) in *.
set (R := e_R (x_e cx)) in *.
assert (HshR : shadow_addr F + 128 <= R) by (unfold SHADOW_OFF in *; lia).
(* the cut's registers *)
unfold hs_at_cx in Hat.
assert (HatA : hs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (r7_L_arm rsegs cx sh np ps cnt es rest r pb))
  by (unfold hs_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (oa_at_get _ _ _ _ _ (LReg 19) (shadow_addr F) HatA ltac:(oa_in)) as R19.
pose proof (oa_at_get _ _ _ _ _ (LReg 23) SHADOW_OFF HatA ltac:(oa_in)) as R23.
pose proof (oa_at_get _ _ _ _ _ (LReg 22) (F + 0xe0) HatA ltac:(oa_in)) as R22.
pose proof (oa_at_get _ _ _ _ _ (LReg 20) (F + 0xa0) HatA ltac:(oa_in)) as R20.
pose proof (oa_at_get _ _ _ _ _ (LReg 18) HS_MULT10 HatA ltac:(oa_in)) as R18.
cbn [hd_at] in R19, R23, R22, R20, R18.
pose proof (oa_at_get _ _ _ _ _ (LReg 10) c Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R10.
pose proof (oa_at_get _ _ _ _ _ (LReg 17) 10 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R17.
pose proof (oa_at_get _ _ _ _ _ (LReg 5) 9 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R5.
pose proof (oa_at_get _ _ _ _ _ (LReg 25) (hs_cur rsegs cx rest r) Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R25.
cbn [hd_at] in R10, R17, R5, R25.
pose proof Hfsh as Hfsh'. unfold hs_fsh_at in Hfsh'. rewrite r7_PG_sh in Hfsh'.
(* ---- the walk ---- *)
eapply SRr_bind.
{ exact (dg_walk B LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 F (x_pos cx) c HJ2 Hown HFa
    R19 R23 R22 R20 R18 R10 R17 R5 ltac:(lia) Hfsh'). }
intros W3 c3 _ (-> & regsG & memG & mdG & -> & HJG & HioG & HregG & HkG & _ & HchG & HshG).
assert (Hkg : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xa0 <= a < F + 0xb8) -> ~ (F + 0xe0 <= a < F + 0xe4) ->
  a <> shadow_addr F + 0x1c -> aview rsegs (w_H W2) memG a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2' H3'. apply HkG; [exact Ha|]. intros [X|[X|X]]; [exact (H1 X) | exact (H2' X) | exact (H3' X)]. }
clear HkG.
apply (HG ly2 S2 W2 regsG memG mdG sh np ps cnt es rr r pb (dec64 (c mod 64)) Hli Hlk).
split; [split; [|exact (proj2 Hbase)]|].
{ (* the journal-and-frame part *)
  unfold hs_core, hs_mid.
  split; [exact HJG|].
  split; [intros q Hq; rewrite (dga_kept regs2 regsG HregG q ltac:(lia)); exact (Hr234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE).
  destruct (Z.eq_dec a (shadow_addr F + 0x1c)) as [Ea|Ea].
  - exfalso. apply HE. left. unfold hd_inw. cbn [hi_w1 headamp_himg_A]. apply Exists_cons_tl. apply Exists_cons_hd.
    cbn [hd_xv fst snd]. fold F. lia.
  - destruct (Z_lt_le_dec a (F + 0x20)) as [La|La]; [apply Hkg; [exact Ha | lia | lia | exact Ea]|].
    destruct (Z_lt_le_dec a (F + 0x158)) as [Lb|Lb]; [|apply Hkg; [exact Ha | lia | lia | exact Ea]].
    exfalso. apply HE. left. unfold hd_inw. cbn [hi_w1 headamp_himg_A]. apply Exists_cons_hd.
    cbn [hd_xv fst snd]. fold F. lia. }
split.
{ (* the (location, value) facts *)
  unfold hs_at_cx, hs_at.
  replace (hs_L_Dc0 rsegs cx sh np ps cnt es ++
    [(LCell XR 0x118, Z.of_nat (length r)); (LReg 20, e_F (x_e cx) + 0xa0); (LReg 27, pb); (LReg 25, hs_cur rsegs cx rest r)])
    with (r7_L_arm rsegs cx sh np ps cnt es rest r pb ++ [(LReg 25, hs_cur rsegs cx rest r)])
    by (unfold r7_L_arm; rewrite <- app_assoc; reflexivity).
  apply Forall_app. split.
  - apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG); [exact HatA|].
    intros f Hf. unfold r7_L_arm, hs_L_Dc0, hs_Rc0, hs_Kc in Hf. cbn [app In] in Hf.
    repeat (destruct Hf as [<-|Hf];
      [ cbn [fst hm_keeps hd_xv]; fold R;
        first [ apply (dga_kept regs2 regsG HregG); lia
              | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Hkg; lia ]
      |]).
    destruct Hf.
  - constructor; [|constructor]. cbn [fst snd hd_at].
    refine (eq_trans (dga_kept regs2 regsG HregG 25 ltac:(lia)) _). exact R25. }
split.
{ (* the frame's shadow: r's byte back to 0xf8 *)
  unfold hs_fsh_at. rewrite r7_PG_sh. rewrite <- (hm_sh_r_out true true false true false false).
  apply (hm_fsh_set rsegs (w_H W2) mem2 (w_H W2) memG F _ 28 1 0xf8 Hfsh').
  - intros j Hj. replace j with 0x1c by lia. exact HshG.
  - intros j Hj Hn. rewrite hm_sh_len in Hj.
    assert (Hj' : j <> 0x1c) by (intros ->; apply Hn; lia).
    apply Hkg; [unfold SHADOW_OFF in *; lia | | | lia].
    + intros X. apply (dga_not_shr F 1024 (shadow_addr F + j) F HFapp); [lia | exact HF4096 | exact HFhi | lia].
    + intros X. apply (dga_not_shr F 1024 (shadow_addr F + j) F HFapp); [lia | exact HF4096 | exact HFhi | lia]. }
split.
{ (* the first block *)
  unfold hs_pp_at in *. eapply (hm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (oa_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply Hkg; [lia | lia | lia |].
  apply (dg_app_not_sh (e_pp (x_e cx)) 0x4d20 x F Hppapp); [lia | exact HF4096 | exact HFhi]. }
split; [exact HchG|].
split.
{ (* e, zeros *)
  eapply (hm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. apply Hkg; [lia | lia | lia |].
  apply (dg_app_not_sh F 1024 x F HFapp); [lia | exact HF4096 | exact HFhi]. }
split; [exact Hkd|].
split.
{ rewrite (r7_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [reflexivity | lia]. }
split; [pose proof (dec64_len (c mod 64)); lia | exact Hpb].
Qed.
End d.
End b.

Print Assumptions r7_dig.
