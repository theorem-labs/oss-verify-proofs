(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 134 of its 183 lines of code are new or changed and 912 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Odd.v at 111d25b4415f (its plan of rebuilding the cut G from a walk's post, and oa_pc_len, oa_at_get) for reac-pw/fuzz_rate's image A; the block is the DIG arm (c < 200, the digits of c mod 64) in place of ODD, with rate's registers, cut states and write set. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Dig.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): lib/AU/RtPgEnt0DefB.v's statement rt7b_dig_stmt over lib/AU/RtPgSegB.v's cuts; the walk lib/AU/RtPgEnt0DigWB.v rt7bd_walk with image B's registers, the class-4 frame, the cell R+0xd8 and s8 = -8 from the DIG cut; G's location list is the arm's without s8; e62 at F+0x210; names rt7_ -> rt7b_, rt7d_ -> rt7bd_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0DigB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; lib/AU/RPgEnt0Def.v's statement r7b_dig_stmt over lib/AU/RPgSeg.v's cuts (no header cells); the walk lib/AU/RPgEnt0DigW.v r7bd_walk with role B's registers (the shadow offset in s11, &r in s5, the multiplier in s7, s10 = -8), the cell R+0xc8 and the real frame of 0x200 bytes; G's location list is the arm's without s10 = -8 and s4 = 1; names rt7b_ -> r7b_, rt7bd_ -> r7bd_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): lib/AU/RPgEnt0Def.v r7b_dig_stmt, the DIG
   block of ent_build's case 0 (pod.h:237-246, c < 200: the digits of c mod 64 into r, reversed into ch, ch's NUL),
   from the cut r7b_cut_DIG at 0x80ce8 to the cut RPgSeg.rs_cut_G at G = 0x80dc8. Proves no function (kind:
   segment lemma).

   HOW. lib/AU/RPgEnt0DigW.v r7bd_walk walks the block over the journal (the plain run P1, the 64 token runs of
   the digits, the reverse copy and the NUL, the plain run P2). This file builds rs_cut_G from r7bd_walk's post:
   the journal-and-frame part (the cut's layout and state unchanged; the walk writes only r, ch and r's shadow byte,
   which lie in the frame's objects and its shadow row of RPgImgA hi_w1), the (location, value) facts (the walk
   changes only a0 .. a7 and no real-frame cell; G's list is the arm's without s10 and s4), the frame's shadow row
   rs_PG, the first block and e62 unchanged, ch holding dec64 (c mod 64) and its NUL, and the model's text by
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSteps RPgSeg RPgEnt0Def.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0DigK RPgEnt0DigW.
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
Ltac r7bd_in := cbn [r7b_L_arm rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app In fst snd];
  repeat (first [left; reflexivity | right]).

(* the first block's image at a pod-loop cut has the block's size [role RPgEnt0Odd.v oa_pc_len] *)
Lemma r7bd_pc_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
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

Lemma r7bd_at_get : forall H mem regs e L l v,
rs_at rsegs H mem regs e L -> In (l, v) L -> rl_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.

Lemma r7b_dig : forall B MT, r7b_dig_stmt rsegs B MT.
Proof.
intros B MT. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold r7b_dig_stmt, r7b_from_DIG.
intros cx POST rest i k Hst HG ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb Hli Hlk Hcut.
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
pose proof asan_consts as (C1 & _ & _ & C4 & _).
assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= e_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : e_R (x_e cx) + 0x200 <= 2 ^ 47) by lia.
assert (HFa : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
destruct (r7bd_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Hown HFa)
  as (Hin4 & HF32 & HF8 & HF0 & HFc & Hceil' & HS0 & HS1 & HSd & HFsh & HFp).
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & Hppapp & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos cx) HAR2 Hpp2 Hin4) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
(* r's shadow byte is no byte of the first block (it lies in the shadow band, the block in application memory) *)
assert (Hshpp : ~ (e_pp (x_e cx) <= shadow_addr (e_F (x_e cx)) + 28 < e_pp (x_e cx) + 19744)).
{ pose proof (rl_fsh_of (e_F (x_e cx)) 224 HF32 ltac:(lia)) as E. change (224 / 8) with 28 in E. rewrite <- E.
  apply (rm_shadow_not_app (e_F (x_e cx) + 224) (e_pp (x_e cx)) 19744); [lia | exact Hppapp]. }
(* the cut's registers and the cell R+0xc8 *)
unfold rs_at_cx in Hat.
assert (HatA : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (r7b_L_arm rsegs cx sh np ps cnt es rest r pb))
  by (unfold rs_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (r7bd_at_get _ _ _ _ _ (LReg 27) SHADOW_OFF HatA ltac:(r7bd_in)) as R27.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 21) (e_F (x_e cx) + 0xe0) HatA ltac:(r7bd_in)) as R21.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 19) (shadow_addr (e_F (x_e cx))) HatA ltac:(r7bd_in)) as R19.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 18) (e_F (x_e cx) + 0xa0) HatA ltac:(r7bd_in)) as R18.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 23) RS_MULT10 HatA ltac:(r7bd_in)) as R23.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 26) (-8) HatA ltac:(r7bd_in)) as R26.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 9) (e_R (x_e cx)) HatA ltac:(r7bd_in)) as R9.
pose proof (r7bd_at_get _ _ _ _ _ (LCell XR 0xc8) (Z.lnot (e_F (x_e cx) + 0xa0)) HatA ltac:(r7bd_in)) as RC8.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 13) c Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R13.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 5) 4 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R5.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 7) 10 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R7.
pose proof (r7bd_at_get _ _ _ _ _ (LReg 28) 9 Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R28.
cbn [rl_at rl_xv] in R27, R21, R19, R18, R23, R26, R9, RC8, R13, R5, R7, R28.
(* ---- the walk ---- *)
eapply SRr_bind.
{ exact (r7bd_walk B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_F (x_e cx)) (x_pos cx) c (e_R (x_e cx)) HJ2 Hown HFa
    R27 R21 R19 R18 R13 R5 R7 R28 R23 R26 R9 ltac:(lia) ltac:(lia) RC8 ltac:(lia) Hfsh). }
intros W3 c3 _ (-> & regsG & memG & mdG & -> & HJG & HioG & HregG & HkG & HfshG & HchG).
apply (HG ly2 S2 W2 regsG memG mdG sh np ps cnt es rr r pb (dec64 (c mod 64)) Hli Hlk).
split; [split; [|exact (proj2 Hbase)]|].
{ (* the journal-and-frame part *)
  unfold rs_core, rs_mid.
  split; [exact HJG|].
  split.
  { intros q Hq.
    rewrite (r7bd_reg_kept regs2 regsG HregG q ltac:(lia) ltac:(destruct Hq as [->|[->| ->]]; reflexivity)).
    exact (Hr234 q Hq). }
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE).
  apply HkG; [exact Ha|].
  intros X. apply HE. left. unfold rl_inw. cbn [hi_w1 role_himg_B].
  unfold r7bd_wW, r7bd_wT, r7bd_wP in X.
  destruct X as [[X|X]|X].
  - apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
  - apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
  - apply Exists_cons_tl, Exists_cons_hd. cbn [rl_xv fst snd]. lia. }
split.
{ (* the (location, value) facts: G's list is the arm's without s10 = -8 and s4 = 1 *)
  unfold rs_at_cx, rs_at.
  apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG).
  { apply Forall_forall. intros f Hf. unfold rs_at in HatA. rewrite Forall_forall in HatA. apply HatA.
    unfold r7b_L_arm, rs_L_Dc. apply in_app_iff in Hf. apply in_app_iff.
    destruct Hf as [Hf|Hf]; [left; apply in_app_iff; left; exact Hf | right; exact Hf]. }
  intros f Hf. unfold rs_L_Dc0, rs_Rc0, rs_Kc, rs_podc in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [fst rm_keeps rl_xv];
      first [ apply (r7bd_reg_kept regs2 regsG HregG); [lia | reflexivity]
            | let j := fresh "j" in let Hj := fresh "Hj" in
              intros j Hj; apply HkG; [lia|]; unfold r7bd_wW, r7bd_wT, r7bd_wP; lia ]
    |]).
  destruct Hf. }
split; [exact HfshG|].
split.
{ (* the first block *)
  unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (r7bd_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply HkG; [lia|]. unfold r7bd_wW, r7bd_wT, r7bd_wP. lia. }
split; [exact HchG|].
split.
{ (* e62, zeros *)
  eapply (rm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. apply HkG; [lia|]. unfold r7bd_wW, r7bd_wT, r7bd_wP. lia. }
split; [exact Hkd|].
split.
{ rewrite (r7b_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [reflexivity | lia]. }
split; [pose proof (dec64_len (c mod 64)); lia | exact Hpb].
Qed.
End b.

Print Assumptions r7bd_pc_len.
Print Assumptions r7b_dig.
