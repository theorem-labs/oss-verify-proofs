(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 336 of its 390 lines of code are new or changed and 907 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bPiece.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the statement is lib/AU/RtPgSegB.v rsb_piece_W7b_stmt at image B's segments; the cuts G and J are image B's (G: t1 = what is left, s2 = &ch, s9 = p, the cursor in R+0x128; J: s2 = &pp->len, s6 = &e62, s10 = the cursor, t1 = what is left; e62 at F+0x210 holds the pod); the frame for locals is class 4; the record is lib/AU/RtPgImgB.v rate_himg_B (the param table 0x9bee0, hi_rz [(0x198, 16)], hi_w1); the walk is lib/AU/RtPgW7bWalkB.v w7b_walk; the memory names are lib/AU/RtPgMemB.v's; the prefix w7_ becomes w7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW7bPieceB.v at 9eff5d44f2fd for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan), as RPgW7b.v: module paths fuzz_rate -> fuzz_role; the segments are lib/AU/Img0.v rsegs; the statement is lib/AU/RPgSeg.v rs_piece_W7b_stmt; the cuts G and J are role B's (G: t1 = what is left, s2 = &ch, s8 = p, the cursor in R+0x118; J: a3 = the cursor, t1 = what is left, s6 = &pp->len, a5 = pp; e62 at F+0x210 holds the pod); the segment's start is lib/A/RPgCSpec.v rl_seg_pre at lib/AU/RPgImgA.v role_himg_B (the param table 0x9a8c0, hi_rz [(0x178, 16)], hi_w1, the real frame 0x200); the cut lists have no header cells; the walk is lib/AU/RPgW7bWalk.v w7b_walk; the memory names are lib/AU/RPgMem.v's. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, which holds the same loaded bytes): the piece
   lemma of ent_build's case 0 after G in LLVMFuzzerTestOneInput, G 0x80dc8 -> J 0x818d8, as lib/AU/RPgSeg.v states
   it (rs_piece_W7b_stmt). Proves no function (kind: segment lemma).

   HOW. The cut G (with the segment's start facts rs_start_M01) gives the walk's facts at G (lib/AU/RPgW7bWalk.v):
   the registers and real-frame cells from the cut's list, ch, e62 and the frame's shadow from the cut, and the
   read-only data (the three strings, the param table cell and its shadow), the parts cell's shadow and rom_view
   from the segment's start, carried to the cut's memory by rs_core (none of their bytes is in the segment's write
   set or in the callees' stack). The walk runs to J; the cut J is rebuilt from its post: the segment frame (the
   walk's write set lies in rs_E1 and the callees' stack), the (location, value) facts (kept, or the walk's J
   registers), the frame's shadow rs_PJ, the first block's image (kept: pp is no byte the walk writes), e62 = the
   pod Model.ent_build makes of the turn's input (RPgW7bFacts.w7b_ent_build_0). The strlen wrapper's contract
   (lib/AU/RPgW7bCall.v w7b_astrlen_realizes at 0x41b60) and __asan_memcpy's (YG0d aintrin_realizes OCpy at
   0x5116c) are the Section's hypotheses. The UBSan trap branches of the piece (0x80ddc, 0x80ec0) and its two
   instrumented checks (0x80df0 / 0x80df4, 0x80e30 / 0x80e38) are refuted inside its blocks (RPgW7bBlkA.v w7b_A1,
   RPgW7bBlkB.v w7b_E1, RPgW7bBlkA2.v w7b_A2). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSeg RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW7bBase RPgW7bBlkA2 RPgW7bKit RPgW7bCall RPgW7bFacts.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW7bWalk.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
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
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

Lemma w7b_r5 : forall {fx : YK11.FPState} (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
getr regs (Z_to_bv 5 z) = getr regs r.
Proof. intros fx regs r z H. subst z. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* membership in a cut's (location, value) list *)
Ltac w7b_inL := cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app In fst snd];
  repeat (first [left; reflexivity | right]).

(* the string facts, carried from the segment's start to the cut: the bytes and their NUL kept, the shadow bytes of
   the string kept, and every shadow word of its hull still readable *)
Lemma w7b_cstr_tr : forall {fx : YK11.FPState} H H' mem mem' a (s : list Z),
rl_cstr rsegs H mem a s ->
(forall b, a <= b <= a + Z.of_nat (length s) -> aview rsegs H' mem' b = aview rsegs H mem b) ->
(forall x, a <= x < a + (Z.of_nat (length s) + 1) ->
 aview rsegs H' mem' (shadow_of_addr SHADOW_OFF x) = aview rsegs H mem (shadow_of_addr SHADOW_OFF x)) ->
(forall y, shadow_addr a / 8 * 8 <= y < shadow_addr (a + (Z.of_nat (length s) + 1) - 1) / 8 * 8 + 8 ->
 aview rsegs H mem y <> None -> aview rsegs H' mem' y <> None) ->
rl_cstr rsegs H' mem' a s.
Proof.
intros fx H H' mem mem' a s (Hb & Hn & Hr & H0 & H1 & Hi & Ham & Hra & Hhv) Kb Ks Kh.
split; [intros i Hi'; rewrite Kb by lia; exact (Hb i Hi')|].
split; [rewrite Kb by lia; exact Hn|].
split; [exact Hr|]. split; [exact H0|]. split; [exact H1|]. split; [exact Hi|]. split; [exact Ham|].
split; [exact (range_addressable_agree _ _ SHADOW_OFF a _ Ks Hra)|].
intros y Hy. exact (Kh y Hy (Hhv y Hy)).
Qed.

(* the cursor src + |rest| - |r| of a suffix r of the input rest at src *)
Lemma w7b_cur_rng : forall (src lft : Z) (rest r : list byte), rs_suffix rest r -> lft = Z.of_nat (length rest) ->
0 < src -> src + lft <= 2 ^ 63 -> 0 <= src + Z.of_nat (length rest) - Z.of_nat (length r) <= 2 ^ 63.
Proof.
intros src lft rest r (j & Hj & Hr) Hl H0 H1.
assert (Hle : (length r <= length rest)%nat) by (rewrite Hr, length_skipn; apply Nat.le_sub_l).
apply Nat2Z.inj_le in Hle. subst lft. lia.
Qed.

(* the pods a pod-loop cut's image holds: at most 32, each body at most 45 bytes *)
Lemma w7b_pc_ents_ok : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es <= 32)%nat ->
(length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\
Forall (fun e0 => (length (e_body e0) <= 96)%nat) (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es (_ & Hkv & Hae & _) Hes Hl.
assert (Wb : forall l, Forall ent_wf l -> Forall (fun e0 => (length (e_body e0) <= 96)%nat) l).
{ intros l H. eapply Forall_impl; [|exact H]. intros e0 (_ & E & S). lia. }
unfold pc_ents. cbn [pc_props pc_open]. unfold first_params.
destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:Hf.
- apply find_some in Hf as [Hin _]. destruct kv as [kk v]. cbn [option_map snd]. destruct v as [z|es'].
  + split; [cbn; lia | constructor].
  + rewrite Forall_forall in Hkv. destruct (Hkv _ Hin) as [_ Hw]. cbn [snd pval_wf] in Hw. split; [exact Hw|].
    apply Wb. rewrite Forall_forall in Hae |- *. intros e0 He0. apply Hae. unfold all_ents.
    apply in_flat_map. exists (kk, PStruct es'). split; [exact Hin | exact He0].
- split; [exact Hl | exact (Wb es Hes)].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W7B_MEMCPY.

(* what the segment's start fixes of the real frame, the frame for locals and the first block *)
Lemma w7b_seg_pre : forall cx, rs_pre rsegs B cx ->
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x200 <= x_sp0 cx /\
  e_R (x_e cx) mod 16 = 0 /\ x_sp0 cx mod 16 = 0 /\ getr (x_regs cx) 2 = w64 (e_R (x_e cx)) /\
  getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ x_sp0 cx <= 2 ^ 47 /\
  In (4, x_pos cx) (x_own cx) /\ e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx) /\
  In (4, x_pos cx) (frames (x_Sc cx)) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  0 < e_pp (x_e cx) /\ e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE.
Proof.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hfsh & Hpp0 & Hpp & Hfl & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & Hp4096 & Hpceil & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil, Happ.
cbn [hi_cid role_himg_B] in Hown, HF.
assert (Hin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & _).
rewrite <- HF in F1, F2. change (fs_frame_bytes 4) with 1024 in F2.
cbn [hi_rsz role_himg_B] in HRs.
unfold T_SEG_STK, ASTACK in *.
repeat split; try assumption; try lia. all: exact (proj2 Happ).
Qed.

Lemma w7b_piece : rs_piece_W7b_stmt rsegs B MT.
Proof.
unfold rs_piece_W7b_stmt. intros cx POST rest i k Hst HJc.
destruct Hst as (Hpre & Hfsh0 & Hcut1 & Hlen0 & Hin0).
pose proof (w7b_seg_pre cx Hpre) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17).
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'.
destruct Hpre' as (HJc0 & _ & _ & _ & _ & HS & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout).
pose proof HJc0 as (HARc & Hlyc & _).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
pose proof (@YM05.alloc_ceiling_value rc) as [CE1 CE2].
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
set (e := x_e cx) in *. set (R := e_R e) in *. set (F := e_F e) in *. set (pp := e_pp e) in *.
assert (Hsp : spZ (x_regs cx) = R) by (unfold spZ; rewrite P5; unfold w64; apply unsigned_lit_small; lia).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HARc P12) as (FM & FA & _).
rewrite <- P11 in FM, FA. change (fs_frame_bytes 4) with 1024 in FA.
pose proof FA as FA'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in FA'.
pose proof P17 as P17'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in P17'.
assert (HshF : 0 <= shadow_addr F /\ shadow_addr F + 128 <= R).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia)).
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold T_SEG_STK, ASTACK in P8. lia. }
(* the frame's shadow at the segment's start is the prologue's: no addressable byte's shadow byte is one of it *)
assert (NF : forall a n, range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF a n ->
  forall x, a <= x < a + n -> ~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 88)).
{ intros a n Ha x Hx. cbn [hi_shA role_himg_B] in Hfsh0.
  exact (rm_ra_not_fsh rsegs _ _ F role_B_shA a n Ha Hfsh0 rm_sh_P0_big x Hx). }
unfold rs_from_G. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs Hlen Hles Hcut.
destruct Hcut as (Hbase & Hat & Hfsh & Hpp & Hch & He0 & Hk0 & Hg & Hchs & Hpb).
pose proof Hbase as Hbase'.
destruct Hbase' as (Hcore & Hin & Hsuf & Hsufrr & Hwf & Hlenq & Hps & Htie & Hsh & Hnp & Hpsnp & Hnp3 & Hsh7 & Hps2 &
  Hcnt & Hesw & Hes32 & Hescnt).
pose proof Hcore as (HJ2 & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
unfold rs_at_cx, rs_at in Hat. fold e in Hat.
(* the memory at G against the segment's start: every byte outside the callees' stack and rs_E1 kept *)
assert (KG : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 16384 <= a < R) -> ~ rs_E1 rsegs cx a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha H1 H2. apply Hmem2; [exact Ha | rewrite Hsp; unfold T_SEG_STK, ASTACK; exact H1 | exact H2]. }
assert (E1img : forall a, in_img rsegs a -> ~ (R - 16384 <= a < R) /\ ~ rs_E1 rsegs cx a).
{ intros a Ha. pose proof (w7b_segs_low a Ha) as L. unfold kLowMemEnd in L. split; [lia|].
  intros [Hw|Hp].
  - unfold rl_inw in Hw. cbn [hi_w1 role_himg_B] in Hw.
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw.
    { assert (Hc : exists cid pos, In (cid, pos) (frames (x_Sc cx)) /\
        frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid).
      { exists 4, (x_pos cx). split; [exact P12|]. rewrite <- P11. change (fs_frame_bytes 4) with 1024. fold e F in Hw. lia. }
      destruct (al_client_img _ _ LAWS _ _ _ _ _ a HARc (or_intror (or_introl Hc))) as [_ Hni]. exact (Hni Ha). }
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw.
    { fold e F in Hw. unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos F 8 ltac:(lia)). lia. }
    repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rl_xv] in Hw; fold e R in Hw; lia|]).
    apply Exists_nil in Hw. exact Hw.
  - assert (Hc : exists p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p <= a < p + req_size n).
    { exists pp, Layout.PP_SIZE. split; [exact P14|]. change (req_size Layout.PP_SIZE) with 19744. fold e pp in Hp.
      rewrite HPS in Hp. lia. }
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HARc (or_introl Hc)) as [_ Hni]. exact (Hni Ha). }
assert (E1sh : forall x, 0 <= x < kHighMemEnd -> ~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 88) ->
  ~ (R - 16384 <= shadow_of_addr SHADOW_OFF x < R) /\ ~ rs_E1 rsegs cx (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx Hnf. pose proof (rm_shadow_band x Hx) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb. split; [lia|].
  intros [Hw|Hp].
  - unfold rl_inw in Hw. cbn [hi_w1 role_himg_B] in Hw.
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw.
    { fold e F in Hw. exact (rm_shadow_not_app x F 1024 Hx FA ltac:(lia)). }
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw; [fold e F in Hw; lia|].
    repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rl_xv] in Hw; fold e R in Hw; lia|]).
    apply Exists_nil in Hw. exact Hw.
  - exact (rm_shadow_not_app x pp Layout.PP_SIZE Hx P17 Hp). }
(* the walk's facts at G *)
assert (Fa2 : frame_addr ly2 4 (x_pos cx) = F).
{ pose proof HJ2 as (_ & Hly2 & _). unfold frame_addr. rewrite P11. unfold frame_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & L1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & L2 & _). rewrite L1, L2. reflexivity. }
assert (A2 : getr regs2 2 = w64 R).
{ rewrite <- (w7b_r5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w7b_r5 (x_regs cx) 2%bv 2 eq_refl). exact P5. }
assert (A3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (w7b_r5 regs2 3%bv 3 eq_refl). rewrite (Hr234 3 (or_intror (or_introl eq_refl))).
  rewrite (w7b_r5 (x_regs cx) 3%bv 3 eq_refl). exact P6. }
assert (A4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (w7b_r5 regs2 4%bv 4 eq_refl). rewrite (Hr234 4 (or_intror (or_intror eq_refl))).
  rewrite (w7b_r5 (x_regs cx) 4%bv 4 eq_refl). exact P7. }
assert (AR_ : forall z v, In (LReg z, v) (rs_L_Dc0 rsegs cx sh np ps cnt es ++
    [(LReg 6, Z.of_nat (length r)); (LReg 18, F + 0xa0); (LReg 24, pb); (LCell XR 0x118, rs_cur rsegs cx rest r)]) ->
  getr regs2 (Z_to_bv 5 z) = w64 v) by (intros z v Hz; exact (w7b_at_reg _ _ _ _ _ z v Hat Hz)).
assert (AC_ : forall o v, In (LCell XR o, v) (rs_L_Dc0 rsegs cx sh np ps cnt es ++
    [(LReg 6, Z.of_nat (length r)); (LReg 18, F + 0xa0); (LReg 24, pb); (LCell XR 0x118, rs_cur rsegs cx rest r)]) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (R + o) 8 (v mod 2 ^ 64)) by (intros o v Ho; exact (w7b_at_cell _ _ _ _ _ o v Hat Ho)).
assert (G9 : getr regs2 9 = w64 R) by (rewrite <- (w7b_r5 regs2 9%bv 9 eq_refl); apply AR_; w7b_inL).
assert (G18 : getr regs2 18 = w64 (F + 0xa0)) by (rewrite <- (w7b_r5 regs2 18%bv 18 eq_refl); apply AR_; w7b_inL).
assert (G19 : getr regs2 19 = w64 (shadow_addr F)) by (rewrite <- (w7b_r5 regs2 19%bv 19 eq_refl); apply AR_; w7b_inL).
assert (G27 : getr regs2 27 = w64 SHADOW_OFF) by (rewrite <- (w7b_r5 regs2 27%bv 27 eq_refl); apply AR_; w7b_inL).
assert (G24 : getr regs2 24 = w64 pb) by (rewrite <- (w7b_r5 regs2 24%bv 24 eq_refl); apply AR_; w7b_inL).
assert (G25 : getr regs2 25 = w64 (F + 0x20)) by (rewrite <- (w7b_r5 regs2 25%bv 25 eq_refl); apply AR_; w7b_inL).
assert (G6 : getr regs2 6 = w64 (Z.of_nat (length r))) by (rewrite <- (w7b_r5 regs2 6%bv 6 eq_refl); apply AR_; w7b_inL).
assert (Hpp63 : pp + Layout.PP_SIZE <= 2 ^ 63) by lia.
assert (C110 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x110) 8 (F + 0x218)).
{ pose proof (AC_ 0x110 (F + 0x218) ltac:(w7b_inL)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (C158 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x158) 8 (F + 0x210)).
{ pose proof (AC_ 0x158 (F + 0x210) ltac:(w7b_inL)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (C130 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x130) 8 (pp + 0x4000)).
{ pose proof (AC_ 0x130 (pp + 0x4000) ltac:(w7b_inL)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (C140 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 pp).
{ pose proof (AC_ 0x140 pp ltac:(w7b_inL)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (Cf0 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf0) 8 (2 ^ 64 - 1 - (F + 0x218))).
{ pose proof (AC_ 0xf0 (Z.lnot (F + 0x218)) ltac:(w7b_inL)) as V.
  rewrite <- (Z.mod_add (Z.lnot (F + 0x218)) 1 (2 ^ 64)) in V by lia.
  replace (Z.lnot (F + 0x218) + 1 * 2 ^ 64) with (2 ^ 64 - 1 - (F + 0x218)) in V by (unfold Z.lnot; lia).
  rewrite Z.mod_small in V by lia. exact V. }
(* the cursor: src + |rest| - |r|, with r a suffix of rest *)
assert (Hcur0 : 0 <= rs_cur rsegs cx rest r <= 2 ^ 63).
{ destruct Hin as (Hq & _ & _ & _ & _ & Hs0 & Hs63 & _). unfold rs_cur.
  exact (w7b_cur_rng _ _ rest r Hsuf Hq Hs0 Hs63). }
assert (C118 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x118) 8 (rs_cur rsegs cx rest r)).
{ pose proof (AC_ 0x118 (rs_cur rsegs cx rest r) ltac:(apply in_or_app; right; cbn [In]; right; right; right; left; reflexivity)) as V.
  rewrite Z.mod_small in V by lia. exact V. }
(* the read-only data and the shadow facts at G, from the segment's start *)
assert (KGimg : forall a, in_img rsegs a -> 0 <= a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha Ha0. destruct (E1img a Ha) as [N1 N2]. pose proof (w7b_segs_low a Ha) as L. unfold kLowMemEnd in L.
  apply KG; [lia | exact N1 | exact N2]. }
assert (Img : forall a, 0x10000 <= a < 0x2f6ac -> in_img rsegs a) by (intros a Ha; exact (w7b_in_seg _ _ a w7b_img_ro Ha)).
assert (Imgr : forall a, 0x9a388 <= a < 0x9c000 -> in_img rsegs a) by (intros a Ha; exact (w7b_in_seg _ _ a w7b_img_relro Ha)).
assert (Hp8 : 0 <= pb mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hpcell : val_mem rsegs (mrestrict (w_H W2) mem2) (W7B_PTAB pb) 8 (w7b_pptr (pb mod 8))).
{ unfold rl_ro_cells in Hcells. cbn [hi_cells role_himg_B] in Hcells. rewrite Forall_forall in Hcells.
  pose proof (Hcells _ (w7b_param_cell (pb mod 8) Hp8)) as V. cbn [fst snd] in V.
  refine (val_mem_kept rsegs (w_H (x_W cx)) (w_H W2) (x_memc cx) mem2 _ 8 _ _ V). intros i0 Hi0. unfold W7B_PTAB.
  apply KGimg; [apply Imgr; lia | lia]. }
assert (Hpra : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (W7B_PTAB pb) 8).
{ cbn [hi_globs role_himg_B] in Hglobs. rewrite Forall_forall in Hglobs.
  assert (G : range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF 0x9a8c0 64)
    by (apply (Hglobs (0x9a8c0, 64)); cbv [role_B_globs In]; repeat (first [left; reflexivity | right])).
  apply (range_addressable_sub _ _ 0x9a8c0 64 (W7B_PTAB pb) 8) in G; [| unfold W7B_PTAB; lia | unfold W7B_PTAB; lia].
  apply (rm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2); [exact G|].
  intros x Hx. destruct (E1sh x ltac:(unfold kHighMemEnd, W7B_PTAB in *; lia) (NF _ _ G x Hx)) as [N1 N2].
  pose proof (rm_shadow_band x ltac:(unfold kHighMemEnd, W7B_PTAB in *; lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
  apply KG; [lia | exact N1 | exact N2]. }
assert (Hra180 : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (R + 0x180) 8).
{ cbn [hi_rz role_himg_B] in Hrz. apply Forall_inv in Hrz. cbn [fst snd] in Hrz.
  apply (range_addressable_sub _ _ (R + 0x178) 16 (R + 0x180) 8) in Hrz; [| lia | lia].
  apply (rm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2); [exact Hrz|].
  intros x Hx. destruct (E1sh x ltac:(unfold kHighMemEnd; lia) (NF _ _ Hrz x Hx)) as [N1 N2].
  pose proof (rm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
  apply KG; [lia | exact N1 | exact N2]. }
assert (Strs : forall a s, In (a, s) role_B_strs -> 0x10000 <= a -> a + Z.of_nat (length s) + 64 < 0x2f6ac ->
  rl_cstr rsegs (w_H W2) mem2 a s).
{ intros a s Hs Ha1 Ha2. cbn [hi_strs role_himg_B] in Hstrs. rewrite Forall_forall in Hstrs.
  pose proof (Hstrs (a, s) Hs) as C. cbn [fst snd] in C. pose proof C as (_ & _ & _ & _ & _ & _ & _ & Cra & _).
  apply (w7b_cstr_tr _ _ (x_memc cx) mem2 a s C).
  - intros b Hb. apply KGimg; [apply Img; lia | lia].
  - intros x Hx. destruct (E1sh x ltac:(unfold kHighMemEnd; lia) (NF _ _ Cra x Hx)) as [N1 N2].
    pose proof (rm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
    apply KG; [lia | exact N1 | exact N2].
  - intros y Hy Hv.
    assert (Hb : kLowMemEnd <= y < kHighMemBeg).
    { apply (w7b_hull_band a (Z.of_nat (length s) + 1)); [lia | lia | unfold kHighMemEnd; lia | exact Hy]. }
    unfold kLowMemEnd, kHighMemBeg in Hb.
    destruct (Z_lt_le_dec y (shadow_addr F)) as [Hy1|Hy1];
    [| destruct (Z_lt_le_dec y (shadow_addr F + 88)) as [Hy2|Hy2]].
    + rewrite KG; [exact Hv | lia | lia |]. intros [Hw|Hp].
      * unfold rl_inw in Hw. cbn [hi_w1 role_himg_B] in Hw.
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw;
          [fold e F in Hw; lia |].
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw; [fold e F in Hw; lia|].
        repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rl_xv] in Hw; fold e R in Hw; lia|]).
        apply Exists_nil in Hw. exact Hw.
      * fold e pp in Hp. rewrite HPS in Hp, P17'. lia.
    + unfold rs_fsh_at, rl_fsh in Hfsh. fold e F in Hfsh.
      pose proof (Hfsh (y - shadow_addr F) ltac:(unfold rs_PG; rewrite rm_sh_len; lia)) as V.
      replace (shadow_addr F + (y - shadow_addr F)) with y in V by lia. rewrite V. discriminate.
    + rewrite KG; [exact Hv | lia | lia |]. intros [Hw|Hp].
      * unfold rl_inw in Hw. cbn [hi_w1 role_himg_B] in Hw.
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw;
          [fold e F in Hw; lia |].
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rl_xv] in Hw; [fold e F in Hw; lia|].
        repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rl_xv] in Hw; fold e R in Hw; lia|]).
        apply Exists_nil in Hw. exact Hw.
      * fold e pp in Hp. rewrite HPS in Hp, P17'. lia. }
assert (Hcs0 : rl_cstr rsegs (w_H W2) mem2 0x20f40 (map (fun b : byte => bv_unsigned b) HPFX)).
{ apply Strs; [exact w7b_hpfx_str | lia | rewrite length_map, w7b_hpfx_len; simpl Z.of_nat; lia]. }
assert (Hcs2 : rl_cstr rsegs (w_H W2) mem2 (w7b_sep pb) (map (fun b : byte => bv_unsigned b) (w7b_sepb pb))).
{ pose proof (w7b_sep_rng pb). pose proof (w7b_sep_len pb). unfold w7b_sepb in *.
  apply Strs; [exact (w7b_sep_str pb) | lia | rewrite length_map; lia]. }
assert (Hcs3 : rl_cstr rsegs (w_H W2) mem2 (w7b_pptr (pb mod 8)) (map (fun b : byte => bv_unsigned b) (w7b_pab pb))).
{ pose proof (w7b_pptr_rng (pb mod 8) Hp8). pose proof (w7b_param_len pb). unfold w7b_pab in *.
  apply Strs; [exact (w7b_param_str (pb mod 8) Hp8) | lia | rewrite length_map; lia]. }
assert (Hro2 : w7b_aro_unowned rsegs B (aview rsegs (w_H W2) mem2)).
{ intros a Ha _ _. assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hs & _ & Hb); exists sg; split; [exact Hs | exact Hb]).
  pose proof (w7b_segs_low a Hi) as L. unfold kLowMemEnd in L.
  rewrite KGimg by (first [exact Hi | lia]). exact (Hrom a Ha). }
(* ---- the walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs RS_G regs2 mem2 md2) with (mkCfg (mkst regs2 (Z_to_bv 64 0x80dc8) mem2 (seg_rom rsegs)) md2).
  apply (w7b_walk B LAWS ASTRLEN AMEMCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 (x_k cx) regs2 mem2 md2 R F (x_pos cx) (rs_cur rsegs cx rest r)
    (Z.of_nat (length r)) pb (pp + 0x4000) pp (2 ^ 64 - 1 - (F + 0x218)) chs);
  try assumption; try lia.
  exact (w7b_chs_nonzero rr chs pb r Hg). }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & J3 & Io3 & Kr3 & Km3 & Pr3 &
  (R13 & R6 & R22 & R15 & Re & Rsh)).
(* ---- the cut J ---- *)
assert (Wr_in : forall a, w7b_WrW R F a -> (R - 16384 <= a < R) \/ rs_E1 rsegs cx a).
{ intros a Ha. unfold w7b_WrW, ESTACK in Ha.
  destruct Ha as [X|[X|[X|[X|X]]]]; [left; lia | right; left | right; left | right; left | right; left];
  unfold rl_inw; cbn [hi_w1 role_himg_B].
  - do 4 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. fold e R. lia.
  - apply Exists_cons_hd. cbn [fst snd rl_xv]. fold e F. lia.
  - apply Exists_cons_hd. cbn [fst snd rl_xv]. fold e F. lia.
  - apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rl_xv]. fold e F. lia. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ w7b_WrW R F a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a)
  by exact Km3.
assert (Kr3' : forall z, 0 < z < 32 -> ~ In (Z_to_bv 5 z) (w7b_clob) ->
  getr regs3 (Z_to_bv 5 z) = getr regs2 (Z_to_bv 5 z)).
{ intros z Hz Hn. apply Kr3; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32;
  rewrite Z.mod_small by lia; lia | exact Hn]. }
apply (HJc ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es rr r (ent_text (w7b_js chs pb) true) Hlen Hles).
split.
- (* rs_pod_base *)
  split; [|exact (proj2 Hbase)].
  split; [exact J3|]. split.
  { intros z Hz. rewrite <- (Hr234 z Hz). apply Kr3'; [destruct Hz as [-> | [-> | -> ]]; lia|].
    destruct Hz as [-> | [-> | -> ]]; unfold w7b_clob; cbv [rl_caller_saved app In]; intros X;
    repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X|]); exact X. }
  split; [exact Hfr2|]. split; [exact Hperm2|]. split; [exact (same_io_trans _ _ _ Hio2 Io3)|]. split; [exact Hmo2|].
  intros a Ha H1 H2. rewrite Hsp in H1. rewrite K3; [| exact Ha |].
  + apply Hmem2; [exact Ha | rewrite Hsp; exact H1 | exact H2].
  + intros X. destruct (Wr_in a X) as [Y|Y]; [unfold T_SEG_STK, ASTACK in H1; lia | exact (H2 Y)].
- split.
  { (* the (location, value) facts *)
    unfold rs_at_cx, rs_at. fold e.
    assert (Kc : forall o v, In (LCell XR o, v) (rs_L_Dc0 rsegs cx sh np ps cnt es ++
        [(LReg 6, Z.of_nat (length r)); (LReg 18, F + 0xa0); (LReg 24, pb); (LCell XR 0x118, rs_cur rsegs cx rest r)]) ->
      0 <= o -> o + 8 <= 0x178 -> rl_at rsegs (w_H W2) mem3 regs3 e (LCell XR o) v).
    { intros o v Ho Ho1 Ho2. apply (rm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 e (LCell XR o) v
        (proj1 (Forall_forall _ _) Hat _ Ho)).
      cbn [rm_keeps rl_xv]. fold R. intros i0 Hi0. apply K3; [lia|]. unfold w7b_WrW, ESTACK.
      unfold in_app in FA. unfold T_SEG_STK, ASTACK in P8. lia. }
    cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app].
    repeat apply Forall_cons; cbn [fst snd].
    all: first
      [ apply Forall_nil
      | (apply Kc; [w7b_inL | lia | lia])
      | (lazymatch goal with |- rl_at _ _ _ _ _ ?l ?v =>
           apply (rm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 e l v
           (proj1 (Forall_forall _ _) Hat (l, v) ltac:(w7b_inL))) end;
         cbn [rm_keeps]; apply Kr3'; [lia | unfold w7b_clob; cbv [rl_caller_saved app In];
         let X := fresh "X" in intros X;
         repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X|]);
         exact X])
      | (cbn [rl_at]; rewrite (w7b_r5 regs3 13%bv 13 eq_refl); exact R13)
      | (cbn [rl_at]; rewrite (w7b_r5 regs3 6%bv 6 eq_refl); exact R6)
      | (cbn [rl_at]; rewrite (w7b_r5 regs3 22%bv 22 eq_refl); exact R22)
      | (cbn [rl_at]; rewrite (w7b_r5 regs3 15%bv 15 eq_refl); exact R15) ].
    }
  split; [exact Rsh|].
  split.
  { (* the first block's image: pp is no byte the walk writes *)
    assert (Hent : (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\
      Forall (fun e0 => (length (e_body e0) <= 96)%nat) (pc_ents (PbCut sh ps (Some es)))).
    { exact (w7b_pc_ents_ok sh ps es Hwf Hesw ltac:(lia)). }
    destruct Hwf as (_ & Hkv & Hae & _).
    assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hkv]; intros kv [_ X]; exact X).
    destruct (pc_buf_len_open sh ps es Hpv Hae Hesw) as [Hbl _].
    assert (Hlimg : Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE).
    { unfold pc_image. apply length_pp_image; [lia | exact (proj1 Hent) | exact (proj2 Hent)]. }
    pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HARc P14 P12) as Hsep.
    rewrite <- P11 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    change (req_size Layout.PP_SIZE) with 19744 in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
    unfold rs_pp_at. apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) mem3); [exact Hpp|].
    intros x Hx. rewrite Hlimg, HPS in Hx. fold e pp in Hx. apply K3; [lia|].
    unfold w7b_WrW, ESTACK. rewrite HPS in P16, P17'. unfold T_SEG_STK, ASTACK in P8.
    assert (Hb : 0x7fff8000 <= shadow_addr F /\ shadow_addr F + 128 <= 0x10007fff8000).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia)).
      assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; lia). lia. }
    lia. }
  split; [exact Re|].
  split; [symmetry; exact (w7b_ent_build_0 rr chs pb r Hk0 Hg Hchs)|].
  rewrite (w7b_ent_text_js chs pb Hchs). unfold ent_wf. cbn [e_type e_size e_body].
  pose proof (w7b_js_len chs pb Hchs) as Hjs. unfold POD_STRING.
  rewrite length_app. cbn [length]. split; [lia|]. split; [lia|]. lia.
Qed.
End b.

Print Assumptions w7b_piece.
