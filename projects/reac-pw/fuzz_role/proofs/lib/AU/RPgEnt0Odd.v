(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 129 of its 184 lines of code are new or changed and 906 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Odd.v at 111d25b4415f for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; RPgEnt0Def / RPgSeg / RPgMem / RPgImgA are lib/A/RtPgEnt0Def.v (rt7_odd_stmt, rt7_cut_ODD, rt7_L_arm, rt7_g_of_cp, rt7_PG_sh), RtPgSeg.v, RtPgMem.v and RtPgImgA.v; the shadow offset is in s2, &ch in s6, and the cursor stays in s9 (no `s9 := s8`: s8 is the one callee-saved register the block changes, and no location of rs_cut_G names it); G is 0x8150c; rate's rt_seg_pre holds no frame shadow; the strlen wrapper's hypothesis is this unit's lib/A/Rt/StrlenDef.v astrlen_realizes STRLEN_ENTRY and __asan_memcpy is 0x51860; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Odd.v at 21da95a5fcd3; image B (images.AsanUbsan): lib/AU/RtPgEnt0DefB.v (rt7b_odd_stmt, rt7b_cut_ODD, rt7b_L_arm, rt7b_g_of_cp), RtPgSegB.v, RtPgMemB.v and RtPgImgB.v for the A files; c is in a3, the shadow offset in s4, &ch in s2, t1 what is left (saved in s8 across the two calls and put back), so the block changes the callee-saved s6 and s8, which no location of rsb_cut_G names (its list is rt7b_L_arm without s8 = -8); the frame for locals is of class 4; G is 0x8160c; the strlen wrapper's hypothesis is lib/AU/RtPgW7bCallB.v w7b_astrlen_realizes at W7B_STRLEN 0x421ec and __asan_memcpy is RtPgStepsB.RTSB_MEMCPY 0x518b8; names oa_ -> oab_, rt7_ -> rt7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0OddB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; lib/AU/RPgEnt0Def.v (r7b_odd_stmt, r7b_cut_ODD, r7b_L_arm, r7b_g_of_cp), RPgSeg.v (no header cells), RPgMem.v and RPgImgA.v for the rate files; the shadow offset is in s11 and t1 is saved in s4 across the two calls and put back, so the block changes the callee-saved s4 and s6, which no location of rs_cut_G names (its list is r7b_L_arm without s10 = -8 and s4 = 1); the real frame is 0x200 bytes; G is 0x80dc8; the strlen wrapper's hypothesis is lib/AU/RPgW7bCall.v w7b_astrlen_realizes at W7B_STRLEN 0x41b60 and checked_memcpy is RPgSteps.RL_MEMCPY 0x5116c; names rt7b_ -> r7b_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): lib/AU/RPgEnt0Def.v
   r7b_odd_stmt, the ODD block of ent_build's case 0 (pod.h:247-248, `const char *o = odd_ch[c % 14];
   memcpy(ch, o, strlen(o) + 1);`), from the cut r7b_cut_ODD at 0x815e0 to the cut RPgSeg.rs_cut_G at
   G = 0x80dc8. Proves no function (kind: segment lemma).

   HOW. lib/AU/RPgEnt0OddC.v ob_at_cut carries the start state's image facts (rom_view, the odd_ch table entry's
   shadow bytes and cell, the string's rl_cstr) to the cut's memory; lib/AU/RPgEnt0OddW.v ob_walk walks the block
   over the journal (three engine runs to the table entry's shadow check, the UBSan test 0x8160c among them, one to
   the strlen call, the strlen wrapper, one run to the checked_memcpy call, the intrinsic, one run to G). This file
   builds rs_cut_G from ob_walk's post: the journal-and-frame part (the cut's layout and state unchanged; the walk
   writes only the callees' stack below R and ch, which lies in the frame's objects of RPgImgA hi_w1), the
   (location, value) facts (callee-saved registers but s4 and s6, t1 and real-frame cells kept), the frame's shadow,
   the first block and e62 unchanged, ch holding odd_ch[c mod 14] and its NUL, and the model's text by
   RPgEnt0Def.r7b_g_of_cp. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSeg RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0Def RPgW7bBase RPgW7bKit RPgW7bCall.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0OddB RPgEnt0OddC RPgEnt0OddW.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
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

(* membership in a concrete location list *)
Ltac oab_in := cbn [r7b_L_arm rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app In fst snd];
  repeat (first [left; reflexivity | right]).

(* the first block's image at a pod-loop cut has the block's size *)
Lemma oab_pc_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (_ & Hk & He & Hl3) Hes Hl. unfold pc_image.
assert (Hk' : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ H]; exact H).
destruct (pc_buf_len_open sh ps es Hk' He Hes) as [Hb _].
assert (HE : (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es)))).
{ unfold pc_ents. cbn [pc_props pc_open].
  destruct (first_params ps) as [[iv|es']|] eqn:E.
  - split; [cbn; lia | constructor].
  - unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
    apply find_some in F as [Hin _]. split.
    + rewrite Forall_forall in Hk'. specialize (Hk' kv Hin). rewrite E in Hk'. exact Hk'.
    + apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
  - split; [lia | exact Hes]. }
destruct HE as [HE1 HE2].
apply Layout.length_pp_image.
- lia.
- exact HE1.
- eapply Forall_impl; [|exact HE2]. intros e (_ & Hbd & Hs). lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma oab_at_get : forall H mem regs e L l v,
rs_at rsegs H mem regs e L -> In (l, v) L -> rl_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RL_MEMCPY.

Lemma r7b_odd : r7b_odd_stmt rsegs B MT.
Proof using ASTRLEN AMEMCPY.
unfold r7b_odd_stmt, r7b_from_ODD.
intros cx POST rest i k Hst HG ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb Hli Hlk Hcut.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hcut as (Hbase & Hat & Hfsh & Hpp & Hz & Hkd & Hcp & Hc & Hpb).
pose proof Hbase as (Hcore & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hes32 & _).
pose proof Hcore as (HJ2 & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof Hst as (Hpre & _).
pose proof Hpre as (HJc & _ & H2 & H3 & H4 & HeS & HR16 & HRS & HRSTK & Hown & HF & _ & _ & Hppin & _).
cbn [hi_rsz hi_cid role_himg_B] in HRS, Hown, HF.
(* the bounds of R, F and pp *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= e_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : e_R (x_e cx) + 0x200 <= 2 ^ 47) by lia.
assert (HFa : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
assert (Hin4 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr, Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin4) as (HF32 & HFapp & _ & _).
rewrite <- HFa in HF32, HFapp. change (fs_frame_bytes 4) with 1024 in HFapp.
pose proof (rl_fbounds (e_F (x_e cx)) HF32 HFapp) as (Fb0 & Fb1 & Fb2 & Fb3 & Fb4 & _).
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos cx) HAR2 Hpp2 Hin4) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep.
assert (Hsp : spZ (x_regs cx) = e_R (x_e cx)) by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
(* the cut's registers *)
unfold rs_at_cx in Hat.
assert (HatA : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (r7b_L_arm rsegs cx sh np ps cnt es rest r pb))
  by (unfold rs_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (oab_at_get _ _ _ _ _ (LReg 27) SHADOW_OFF HatA ltac:(oab_in)) as R27. cbn [rl_at] in R27.
pose proof (oab_at_get _ _ _ _ _ (LReg 18) (e_F (x_e cx) + 0xa0) HatA ltac:(oab_in)) as R18. cbn [rl_at] in R18.
pose proof (oab_at_get _ _ _ _ _ (LReg 13) c Hat
  ltac:(apply in_or_app; right; cbn [In]; left; reflexivity)) as R13.
cbn [rl_at] in R13.
(* the start facts at the cut's memory *)
destruct (ob_at_cut B MT cx rest ly2 S2 W2 regs2 mem2 md2 Hst Hcore Hfsh) as (Hrom2 & Hodd).
assert (Hm : 0 <= c mod 14 < 14) by (apply Z.mod_pos_bound; lia).
destruct (Hodd (c mod 14) Hm) as (Hra2 & Hcell2 & Hcs2).
pose proof Hfsh as Hfsh'. unfold rs_fsh_at, rs_PG in Hfsh'.
(* ---- the walk ---- *)
eapply SRr_bind.
{ exact (ob_walk B ASTRLEN AMEMCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) c HJ2
    (eq_trans (Hr234 2 (or_introl eq_refl)) H2) (eq_trans (Hr234 3 (or_intror (or_introl eq_refl))) H3)
    (eq_trans (Hr234 4 (or_intror (or_intror eq_refl))) H4) R27 R13 R18 ltac:(lia) HR16 ltac:(lia) HRSTK Hown HFa
    Hfsh' Hrom2 Hra2 Hcell2 Hcs2). }
intros W3 c3 _ (-> & regsG & memG & mdG & -> & HJG & HioG & HregG & Ht1G & HkG & HchG).
pose proof (ob_len_le (c mod 14) Hm) as Hol. unfold ob_len in HkG.
assert (Hkg : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - 2 * ESTACK <= a < e_R (x_e cx)) ->
  ~ (e_F (x_e cx) + 0xa0 <= a < e_F (x_e cx) + 0xa0 + Z.of_nat (length (ob_str (c mod 14))) + 1) ->
  aview rsegs (w_H W2) memG a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H1'. apply HkG; [exact Ha|]. intros [X|X]; [exact (H1 X) | exact (H1' X)]. }
clear HkG.
apply (HG ly2 S2 W2 regsG memG mdG sh np ps cnt es rr r pb (ob_str (c mod 14)) Hli Hlk).
split; [split; [|exact (proj2 Hbase)]|].
{ (* the journal-and-frame part *)
  unfold rs_core, rs_mid.
  split; [exact HJG|].
  split; [intros q Hq; rewrite (HregG q ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)); exact (Hr234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE). rewrite Hsp in Hs.
  apply Hkg; [exact Ha | lia |].
  intros X. apply HE. left. unfold rl_inw. cbn [hi_w1 role_himg_B]. apply Exists_cons_hd. cbn [rl_xv fst snd]. lia. }
split.
{ (* the (location, value) facts: rs_cut_G's list is r7b_L_arm without s10 = -8 and s4 = 1 *)
  unfold rs_at_cx, rs_at.
  apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG).
  { unfold rs_at, r7b_L_arm, rs_L_Dc in HatA. apply Forall_app in HatA as [HA1 HA2].
    apply Forall_app in HA1 as [HA0 _]. apply Forall_app. split; [exact HA0 | exact HA2]. }
  intros f Hf. unfold rs_L_Dc0, rs_Rc0, rs_Kc, rs_podc in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [fst rm_keeps rl_xv];
      first [ apply HregG; [unfold acallee_saved; lia | lia | lia]
            | exact Ht1G
            | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Hkg; lia ]
    |]).
  destruct Hf. }
split.
{ (* the frame's shadow *)
  unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. unfold rs_PG. rewrite rm_sh_len. intros j Hj.
  apply Hkg; lia. }
split.
{ (* the first block *)
  unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (oab_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply Hkg; lia. }
split; [exact HchG|].
split.
{ (* e62, zeros *)
  eapply (rm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. apply Hkg; lia. }
split; [exact Hkd|].
split.
{ rewrite (r7b_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [lia | reflexivity]. }
split; [exact Hol | exact Hpb].
Qed.
(* inside the Section: the two runtime contracts ASTRLEN and AMEMCPY are its only hypotheses *)
Print Assumptions r7b_odd.
End d.
End b.

Print Assumptions r7b_odd.
