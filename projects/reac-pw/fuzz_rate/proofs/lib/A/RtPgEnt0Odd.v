(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths and module names changed; 129 of its 181 lines of code are new or changed and 538 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Odd.v at 111d25b4415f for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; RPgEnt0Def / RPgSeg / RPgMem / RPgImgA are lib/A/RtPgEnt0Def.v (rt7_odd_stmt, rt7_cut_ODD, rt7_L_arm, rt7_g_of_cp, rt7_PG_sh), RtPgSeg.v, RtPgMem.v and RtPgImgA.v; the shadow offset is in s2, &ch in s6, and the cursor stays in s9 (no `s9 := s8`: s8 is the one callee-saved register the block changes, and no location of rs_cut_G names it); G is 0x8150c; rate's rt_seg_pre holds no frame shadow; the strlen wrapper's hypothesis is this unit's lib/A/Rt/StrlenDef.v astrlen_realizes STRLEN_ENTRY and __asan_memcpy is 0x51860; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): lib/A/RtPgEnt0Def.v
   rt7_odd_stmt, the ODD block of ent_build's case 0 (pod.h:247-248, `const char *o = odd_ch[c % 14];
   memcpy(ch, o, strlen(o) + 1);`), from the cut rt7_cut_ODD at 0x81b6c to the cut RtPgSeg.rs_cut_G at G = 0x8150c.
   Proves no function (kind: segment lemma).

   HOW. lib/A/RtPgEnt0OddC.v o_at_cut carries the start state's image facts (rom_view, the odd_ch table entry's
   shadow bytes and cell, the string's rt_cstr) to the cut's memory; lib/A/RtPgEnt0OddW.v o_walk walks the block over
   the journal (two engine runs to the table entry's shadow check, one to the strlen call, the strlen wrapper, one run
   to the __asan_memcpy call, the intrinsic, one run to G). This file builds rs_cut_G from o_walk's post: the
   journal-and-frame part (the cut's layout and state unchanged; the walk writes only the callees' stack below R and
   ch, which lies in the frame's objects of RtPgImgA hi_w1), the (location, value) facts (callee-saved registers but
   s8 and real-frame cells kept), the frame's shadow, the first block and e unchanged, ch holding odd_ch[c mod 14]
   and its NUL, and the model's text by RtPgEnt0Def.rt7_g_of_cp. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgEnt0Def RtPgW7bBase RtPgW7bKit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgEnt0OddB RtPgEnt0OddC RtPgEnt0OddW.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

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
Ltac oa_in := cbn [rt7_L_arm rs_L_Dc0 rs_Rc0 rs_Kc rs_Hc rs_podc app In fst snd]; repeat (first [left; reflexivity | right]).

(* the first block's image at a pod-loop cut has the block's size *)
Lemma oa_pc_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
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

Lemma oa_at_get : forall H mem regs e L l v,
rs_at rsegs H mem regs e L -> In (l, v) L -> rt_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : astrlen_realizes rsegs B STRLEN_ENTRY.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x51860.

Lemma rt7_odd : rt7_odd_stmt rsegs B MT.
Proof using ASTRLEN AMEMCPY.
unfold rt7_odd_stmt, rt7_from_ODD.
intros cx POST rest i k Hst HG ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb Hli Hlk Hcut.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hcut as (Hbase & Hat & Hfsh & Hpp & Hz & Hkd & Hcp & Hc & Hpb).
pose proof Hbase as (Hcore & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hes32 & _).
pose proof Hcore as (HJ2 & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof Hst as (Hpre & _ & _ & _ & _).
pose proof Hpre as (HJc & _ & H2 & H3 & H4 & HeS & HR16 & HRS & HRSTK & Hown & HF & _ & Hppin & _).
cbn [hi_rsz hi_cid rate_himg_A] in HRS, Hown, HF.
(* the bounds of R, F and pp *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= q_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : q_R (x_e cx) + 0x1e0 <= 2 ^ 47) by lia.
assert (HFa : q_F (x_e cx) = frame_addr ly2 3 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
assert (Hin3 : In (3, x_pos cx) (frames S2)) by (rewrite Hfr, Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 3 (x_pos cx) HAR2 Hin3) as (HF32 & HFapp & _ & _).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 3 (x_pos cx) HAR2 Hin3) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, HFapp, HF4096, HFceil. change (fs_frame_bytes 3) with 512 in HFapp, HFceil.
assert (Hpp2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 3 (x_pos cx) HAR2 Hpp2 Hin3) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 3) with 512 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep.
assert (Hsp : spZ (x_regs cx) = q_R (x_e cx)) by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
(* the cut's registers *)
unfold rs_at_cx in Hat.
assert (HatA : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (rt7_L_arm rsegs cx sh np ps cnt es rest r pb))
  by (unfold rs_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (oa_at_get _ _ _ _ _ (LReg 18) SHADOW_OFF HatA ltac:(oa_in)) as R18. cbn [rt_at] in R18.
pose proof (oa_at_get _ _ _ _ _ (LReg 22) (q_F (x_e cx) + 0xa0) HatA ltac:(oa_in)) as R22. cbn [rt_at] in R22.
pose proof (oa_at_get _ _ _ _ _ (LReg 10) c Hat
  ltac:(apply in_or_app; right; cbn [In]; left; reflexivity)) as R10.
cbn [rt_at] in R10.
(* the start facts at the cut's memory *)
destruct (o_at_cut B MT cx rest ly2 S2 W2 regs2 mem2 md2 Hst Hcore Hfsh) as (Hrom2 & Hodd).
assert (Hm : 0 <= c mod 14 < 14) by (apply Z.mod_pos_bound; lia).
destruct (Hodd (c mod 14) Hm) as (Hra2 & Hcell2 & Hcs2).
pose proof Hfsh as Hfsh'. unfold rs_fsh_at in Hfsh'. rewrite rt7_PG_sh in Hfsh'.
(* ---- the walk ---- *)
eapply SRr_bind.
{ exact (o_walk B ASTRLEN AMEMCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx) c HJ2
    (eq_trans (Hr234 2 (or_introl eq_refl)) H2) (eq_trans (Hr234 3 (or_intror (or_introl eq_refl))) H3)
    (eq_trans (Hr234 4 (or_intror (or_intror eq_refl))) H4) R18 R10 R22 ltac:(lia) HR16 ltac:(lia) HRSTK Hown HFa
    Hfsh' Hrom2 Hra2 Hcell2 Hcs2). }
intros W3 c3 _ (-> & regsG & memG & mdG & -> & HJG & HioG & HregG & HkG & HchG).
pose proof (o_len_le (c mod 14) Hm) as Hol. unfold o_len in HkG.
assert (Hkg : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - 2 * ESTACK <= a < q_R (x_e cx)) ->
  ~ (q_F (x_e cx) + 0xa0 <= a < q_F (x_e cx) + 0xa0 + Z.of_nat (length (o_str (c mod 14))) + 1) ->
  aview rsegs (w_H W2) memG a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H1'. apply HkG; [exact Ha|]. intros [X|X]; [exact (H1 X) | exact (H1' X)]. }
clear HkG.
apply (HG ly2 S2 W2 regsG memG mdG sh np ps cnt es rr r pb (o_str (c mod 14)) Hli Hlk).
split; [split; [|exact (proj2 Hbase)]|].
{ (* the journal-and-frame part *)
  unfold rs_core, rs_mid.
  split; [exact HJG|].
  split; [intros q Hq; rewrite (HregG q ltac:(unfold acallee_saved; lia) ltac:(lia)); exact (Hr234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE). rewrite Hsp in Hs.
  apply Hkg; [exact Ha | lia |].
  intros X. apply HE. left. unfold rt_inw. cbn [hi_w1 rate_himg_A]. apply Exists_cons_hd. cbn [rt_xv fst snd]. lia. }
split.
{ (* the (location, value) facts: rs_cut_G's list is rt7_L_arm *)
  unfold rs_at_cx, rs_at.
  apply (rtm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG); [exact HatA|].
  intros f Hf. unfold rs_L_Dc0, rs_Rc0, rs_Kc, rs_Hc, rs_podc in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [fst rtm_keeps rt_xv];
      first [ apply HregG; [unfold acallee_saved; lia | lia]
            | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Hkg; lia ]
    |]).
  destruct Hf. }
split.
{ (* the frame's shadow *)
  unfold rs_fsh_at in *. eapply rtm_fsh_kept; [exact Hfsh|]. rewrite rt7_PG_sh, rtm_sh_len. intros j Hj.
  pose proof (Z.mul_div_le (q_F (x_e cx)) 8 ltac:(lia)) as Hd. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
  apply Hkg; unfold shadow_addr, SHADOW_OFF; lia. }
split.
{ (* the first block *)
  unfold rs_pp_at in *. eapply (rtm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (oa_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply Hkg; lia. }
split; [exact HchG|].
split.
{ (* e, zeros *)
  eapply (rtm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. apply Hkg; lia. }
split; [exact Hkd|].
split.
{ rewrite (rt7_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [lia | reflexivity]. }
split; [exact Hol | exact Hpb].
Qed.
End d.
End b.

Print Assumptions rt7_odd.
