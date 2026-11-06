(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths changed; 148 of its 197 lines of code are new or changed and 541 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): lib/A/RPgEnt0Def.v r7_dig_stmt, the DIG block of
   ent_build's case 0 (pod.h:237-246: the decimal text of c mod 64 into ch with its NUL, through r[4]), from the cut
   r7_cut_DIG at 0x80c00 to the cut RPgSeg.rs_cut_G at G = 0x80d14. Proves no function (kind: segment lemma).

   HOW. lib/A/RPgEnt0DigW.v dg_walk walks the block over the journal (r into scope, the digits and the reverse into
   ch, r out of scope again). This file builds rs_cut_G from dg_walk's post: the journal-and-frame part (the cut's
   layout and state unchanged; the walk writes only ch, r and r's shadow byte, which lie in the frame's objects and
   its shadow row of RPgImgA hi_w1), the (location, value) facts (every register but a0 .. a7 and every real-frame
   cell kept), the frame's shadow (r's byte back to 0xf8, so the row is rs_PG again), the first block and e
   unchanged, ch holding dec64 (c mod 64) and its NUL, and the model's text by RPgEnt0Def.r7_g_of_cp. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgEnt0Def RPgW7bBase RPgEnt0Odd RPgEnt0DigW.
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
Lemma dga_not_shr : forall lo len a F, in_app lo len -> lo <= a < lo + len -> 4096 <= F -> F + 512 <= DG_FHI ->
~ (shadow_addr F <= a < shadow_addr F + 64).
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
pose proof Hpre as (HJc & _ & H2 & H3 & H4 & HeS & HR16 & HRS & HRSTK & Hown & HF & _ & _ & Hppin & _).
cbn [hi_rsz hi_cid role_himg_A] in HRS, Hown, HF.
(* the bounds of R, F and pp *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= e_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : e_R (x_e cx) + 0x1a0 <= 2 ^ 47) by lia.
assert (HFa : e_F (x_e cx) = frame_addr ly2 3 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
assert (Hin3 : In (3, x_pos cx) (frames S2)) by (rewrite Hfr, Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 3 (x_pos cx) HAR2 Hin3) as (HF32 & HFapp & _ & _).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 3 (x_pos cx) HAR2 Hin3) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, HFapp, HF4096, HFceil. change (fs_frame_bytes 3) with 512 in HFapp, HFceil.
assert (HFhi : e_F (x_e cx) + 512 <= DG_FHI) by (unfold DG_FHI; lia).
pose proof (dg_sh_bounds _ HF4096 HFhi) as (SB0 & SB1).
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & Hppapp & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 3 (x_pos cx) HAR2 Hpp2 Hin3) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 3) with 512 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
set (F := e_F (x_e cx)) in *.
set (R := e_R (x_e cx)) in *.
assert (HshR : shadow_addr F + 64 <= R) by (unfold SHADOW_OFF in *; lia).
(* the cut's registers *)
unfold rs_at_cx in Hat.
assert (HatA : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (r7_L_arm rsegs cx sh np ps cnt es rest r pb))
  by (unfold rs_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (oa_at_get _ _ _ _ _ (LReg 19) (shadow_addr F) HatA ltac:(oa_in)) as R19.
pose proof (oa_at_get _ _ _ _ _ (LReg 23) SHADOW_OFF HatA ltac:(oa_in)) as R23.
pose proof (oa_at_get _ _ _ _ _ (LReg 22) (F + 0xe0) HatA ltac:(oa_in)) as R22.
pose proof (oa_at_get _ _ _ _ _ (LReg 20) (F + 0xa0) HatA ltac:(oa_in)) as R20.
pose proof (oa_at_get _ _ _ _ _ (LReg 18) RS_MULT10 HatA ltac:(oa_in)) as R18.
cbn [rl_at] in R19, R23, R22, R20, R18.
pose proof (oa_at_get _ _ _ _ _ (LReg 10) c Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R10.
pose proof (oa_at_get _ _ _ _ _ (LReg 17) 10 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R17.
pose proof (oa_at_get _ _ _ _ _ (LReg 5) 9 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R5.
pose proof (oa_at_get _ _ _ _ _ (LReg 25) (rs_cur rsegs cx rest r) Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R25.
cbn [rl_at] in R10, R17, R5, R25.
pose proof Hfsh as Hfsh'. unfold rs_fsh_at in Hfsh'. rewrite r7_PG_sh in Hfsh'.
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
  unfold rs_core, rs_mid.
  split; [exact HJG|].
  split; [intros q Hq; rewrite (dga_kept regs2 regsG HregG q ltac:(lia)); exact (Hr234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE).
  destruct (Z.eq_dec a (shadow_addr F + 0x1c)) as [Ea|Ea].
  - exfalso. apply HE. left. unfold rl_inw. cbn [hi_w1 role_himg_A]. apply Exists_cons_tl. apply Exists_cons_hd.
    cbn [rl_xv fst snd]. fold F. lia.
  - destruct (Z_lt_le_dec a (F + 0x20)) as [La|La]; [apply Hkg; [exact Ha | lia | lia | exact Ea]|].
    destruct (Z_lt_le_dec a (F + 0x180)) as [Lb|Lb]; [|apply Hkg; [exact Ha | lia | lia | exact Ea]].
    exfalso. apply HE. left. unfold rl_inw. cbn [hi_w1 role_himg_A]. apply Exists_cons_hd.
    cbn [rl_xv fst snd]. fold F. lia. }
split.
{ (* the (location, value) facts *)
  unfold rs_at_cx, rs_at.
  replace (rs_L_Dc0 rsegs cx sh np ps cnt es ++
    [(LCell XR 0xf8, Z.of_nat (length r)); (LReg 20, e_F (x_e cx) + 0xa0); (LReg 27, pb); (LReg 25, rs_cur rsegs cx rest r)])
    with (r7_L_arm rsegs cx sh np ps cnt es rest r pb ++ [(LReg 25, rs_cur rsegs cx rest r)])
    by (unfold r7_L_arm; rewrite <- app_assoc; reflexivity).
  apply Forall_app. split.
  - apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG); [exact HatA|].
    intros f Hf. unfold r7_L_arm, rs_L_Dc0, rs_Rc0, rs_Kc in Hf. cbn [app In] in Hf.
    repeat (destruct Hf as [<-|Hf];
      [ cbn [fst rm_keeps rl_xv]; fold R;
        first [ apply (dga_kept regs2 regsG HregG); lia
              | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Hkg; lia ]
      |]).
    destruct Hf.
  - constructor; [|constructor]. cbn [fst snd rl_at].
    refine (eq_trans (dga_kept regs2 regsG HregG 25 ltac:(lia)) _). exact R25. }
split.
{ (* the frame's shadow: r's byte back to 0xf8 *)
  unfold rs_fsh_at. rewrite r7_PG_sh. rewrite <- (rm_sh_r_out true true false true false).
  apply (rm_fsh_set rsegs (w_H W2) mem2 (w_H W2) memG F _ 28 1 0xf8 Hfsh').
  - intros j Hj. replace j with 0x1c by lia. exact HshG.
  - intros j Hj Hn. rewrite rm_sh_len in Hj.
    assert (Hj' : j <> 0x1c) by (intros ->; apply Hn; lia).
    apply Hkg; [unfold SHADOW_OFF in *; lia | | | lia].
    + intros X. apply (dga_not_shr F 512 (shadow_addr F + j) F HFapp); [lia | exact HF4096 | exact HFhi | lia].
    + intros X. apply (dga_not_shr F 512 (shadow_addr F + j) F HFapp); [lia | exact HF4096 | exact HFhi | lia]. }
split.
{ (* the first block *)
  unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (oa_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply Hkg; [lia | lia | lia |].
  apply (dg_app_not_sh (e_pp (x_e cx)) 0x4d20 x F Hppapp); [lia | exact HF4096 | exact HFhi]. }
split; [exact HchG|].
split.
{ (* e, zeros *)
  eapply (rm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. apply Hkg; [lia | lia | lia |].
  apply (dg_app_not_sh F 512 x F HFapp); [lia | exact HF4096 | exact HFhi]. }
split; [exact Hkd|].
split.
{ rewrite (r7_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [reflexivity | lia]. }
split; [pose proof (dec64_len (c mod 64)); lia | exact Hpb].
Qed.
End d.
End b.

Print Assumptions r7_dig.
