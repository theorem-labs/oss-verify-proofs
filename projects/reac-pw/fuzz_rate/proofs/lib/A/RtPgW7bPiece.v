(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v; 333 of its 385 lines of code are new or changed and 538 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the piece lemma of ent_build's case 0 after G
   in LLVMFuzzerTestOneInput, G 0x8150c -> J 0x81e00, as lib/A/RtPgSeg.v states it (rs_piece_W7b_stmt). Proves no
   function (kind: segment lemma).

   HOW. The cut G (with the segment's start facts rs_start_M01) gives the walk's facts at G (lib/A/RtPgW7bWalk.v):
   the registers and real-frame cells from the cut's list, ch, e and the frame's shadow from the cut, and the
   read-only data (the three strings, the param table cell and its shadow), the parts cell's shadow and rom_view
   from the segment's start, carried to the cut's memory by rs_core (none of their bytes is in the segment's write
   set or in the callees' stack). The walk runs to J; the cut J is rebuilt from its post: the segment frame (the
   walk's write set lies in rs_E1 and the callees' stack), the (location, value) facts (kept, or the walk's J
   registers), the frame's shadow rs_PJ, the first block's image (kept: pp is no byte the walk writes), e = the pod
   Model.ent_build makes of the turn's input (RtPgW7bFacts.w7_ent_build_0). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW7bBase RtPgW7bBlkA2 RtPgW7bKit RtPgW7bCall RtPgW7bFacts.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW7bWalk.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef WrapRo.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

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
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

Lemma w7_r5 : forall {fx : YK11.FPState} (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
getr regs (Z_to_bv 5 z) = getr regs r.
Proof. intros fx regs r z H. subst z. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* membership in a cut's (location, value) list *)
Ltac w7_in := cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_Hc rs_podc app In fst snd];
  repeat (first [left; reflexivity | right]).

(* the string facts, carried from the segment's start to the cut: the bytes and their NUL kept, the shadow bytes of
   the string kept, and every shadow word of its hull still readable *)
Lemma w7_cstr_tr : forall {fx : YK11.FPState} H H' mem mem' a (s : list Z),
rt_cstr rsegs H mem a s ->
(forall b, a <= b <= a + Z.of_nat (length s) -> aview rsegs H' mem' b = aview rsegs H mem b) ->
(forall x, a <= x < a + (Z.of_nat (length s) + 1) ->
 aview rsegs H' mem' (shadow_of_addr SHADOW_OFF x) = aview rsegs H mem (shadow_of_addr SHADOW_OFF x)) ->
(forall y, shadow_addr a / 8 * 8 <= y < shadow_addr (a + (Z.of_nat (length s) + 1) - 1) / 8 * 8 + 8 ->
 aview rsegs H mem y <> None -> aview rsegs H' mem' y <> None) ->
rt_cstr rsegs H' mem' a s.
Proof.
intros fx H H' mem mem' a s (Hb & Hn & Hr & H0 & H1 & Hi & Ham & Hra & Hhv) Kb Ks Kh.
split; [intros i Hi'; rewrite Kb by lia; exact (Hb i Hi')|].
split; [rewrite Kb by lia; exact Hn|].
split; [exact Hr|]. split; [exact H0|]. split; [exact H1|]. split; [exact Hi|]. split; [exact Ham|].
split; [exact (range_addressable_agree _ _ SHADOW_OFF a _ Ks Hra)|].
intros y Hy. exact (Kh y Hy (Hhv y Hy)).
Qed.

(* the pods a pod-loop cut's image holds: at most 32, each body at most 45 bytes *)
Lemma w7_pc_ents_ok : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es <= 32)%nat ->
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
Hypothesis ASTRLEN : astrlen_realizes rsegs B W7_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.

(* what the segment's start fixes of the real frame, the frame for locals and the first block *)
Lemma w7_pre : forall cx, rs_pre rsegs B cx ->
  x_sp0 cx - x_STK cx <= q_R (x_e cx) - T_SEG_STK /\ q_R (x_e cx) + 0x1e0 <= x_sp0 cx /\
  q_R (x_e cx) mod 16 = 0 /\ x_sp0 cx mod 16 = 0 /\ getr (x_regs cx) 2 = w64 (q_R (x_e cx)) /\
  getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B) /\
  alloc_ceiling + T_SEG_STK <= q_R (x_e cx) /\ x_sp0 cx <= 2 ^ 47 /\
  In (3, x_pos cx) (x_own cx) /\ q_F (x_e cx) = frame_addr (x_lyc cx) 3 (x_pos cx) /\
  In (3, x_pos cx) (frames (x_Sc cx)) /\ q_F (x_e cx) + 512 <= alloc_ceiling /\
  In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  0 < q_pp (x_e cx) /\ q_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\ in_app (q_pp (x_e cx)) Layout.PP_SIZE.
Proof.
intros cx Hpre. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hpp0 & Hpp & Hhdr & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout & Hi32 & Hu64).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & Hp4096 & Hpceil & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil, Happ.
cbn [hi_cid rate_himg_A] in Hown, HF.
assert (Hin : In (3, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & _).
rewrite <- HF in F1, F2. change (fs_frame_bytes 3) with 512 in F2.
cbn [hi_rsz rate_himg_A] in HRs.
unfold T_SEG_STK, ASTACK in *.
repeat split; try assumption; try lia. all: exact (proj2 Happ).
Qed.

Lemma w7_piece : rs_piece_W7b_stmt rsegs B MT.
Proof.
unfold rs_piece_W7b_stmt. intros cx POST rest i k Hst HJc.
destruct Hst as (Hpre & Hfsh0 & Hcut1 & Hlen0 & Hin0).
pose proof (w7_pre cx Hpre) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17).
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (HJc0 & _ & _ & _ & _ & HS & _ & _ & _ & _ & _ & _ & _ & _ & Hro & Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout & _).
pose proof HJc0 as (HARc & Hlyc & _).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
pose proof (@YM05.alloc_ceiling_value rc) as [CE1 CE2].
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
set (e := x_e cx) in *. set (R := q_R e) in *. set (F := q_F e) in *. set (pp := q_pp e) in *.
assert (Hsp : spZ (x_regs cx) = R) by (unfold spZ; rewrite P5; unfold w64; apply unsigned_lit_small; lia).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HARc P12) as (FM & FA & _).
rewrite <- P11 in FM, FA. change (fs_frame_bytes 3) with 512 in FA.
pose proof FA as FA'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in FA'.
pose proof P17 as P17'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in P17'.
assert (HshF : 0 <= shadow_addr F /\ shadow_addr F + 64 <= R).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia)).
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold T_SEG_STK, ASTACK in P8. lia. }
(* the frame's shadow at the segment's start is the prologue's: no addressable byte's shadow byte is one of it *)
assert (NF : forall a n, range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF a n ->
  forall x, a <= x < a + n -> ~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 56)).
{ intros a n Ha x Hx. cbn [hi_shA rate_himg_A] in Hfsh0.
  exact (rtm_ra_not_fsh rsegs _ _ F rate_A_shA a n Ha Hfsh0 rtm_sh_P0_big x Hx). }
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
{ intros a Ha. pose proof (w7_segs_low a Ha) as L. unfold kLowMemEnd in L. split; [lia|].
  intros [Hw|Hp].
  - unfold rt_inw in Hw. cbn [hi_w1 rate_himg_A] in Hw.
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw.
    { assert (Hc : exists cid pos, In (cid, pos) (frames (x_Sc cx)) /\
        frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid).
      { exists 3, (x_pos cx). split; [exact P12|]. rewrite <- P11. change (fs_frame_bytes 3) with 512. fold e F in Hw. lia. }
      destruct (al_client_img _ _ LAWS _ _ _ _ _ a HARc (or_intror (or_introl Hc))) as [_ Hni]. exact (Hni Ha). }
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw.
    { fold e F in Hw. unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos F 8 ltac:(lia)). lia. }
    repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rt_xv] in Hw; fold e R in Hw; lia|]).
    apply Exists_nil in Hw. exact Hw.
  - assert (Hc : exists p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p <= a < p + req_size n).
    { exists pp, Layout.PP_SIZE. split; [exact P14|]. change (req_size Layout.PP_SIZE) with 19744. fold e pp in Hp.
      rewrite HPS in Hp. lia. }
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HARc (or_introl Hc)) as [_ Hni]. exact (Hni Ha). }
assert (E1sh : forall x, 0 <= x < kHighMemEnd -> ~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 56) ->
  ~ (R - 16384 <= shadow_of_addr SHADOW_OFF x < R) /\ ~ rs_E1 rsegs cx (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx Hnf. pose proof (rtm_shadow_band x Hx) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb. split; [lia|].
  intros [Hw|Hp].
  - unfold rt_inw in Hw. cbn [hi_w1 rate_himg_A] in Hw.
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw.
    { fold e F in Hw. exact (rtm_shadow_not_app x F 512 Hx FA ltac:(lia)). }
    apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw; [fold e F in Hw; lia|].
    repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rt_xv] in Hw; fold e R in Hw; lia|]).
    apply Exists_nil in Hw. exact Hw.
  - exact (rtm_shadow_not_app x pp Layout.PP_SIZE Hx P17 Hp). }
(* the walk's facts at G *)
assert (Fa2 : frame_addr ly2 3 (x_pos cx) = F).
{ pose proof HJ2 as (_ & Hly2 & _). unfold frame_addr. rewrite P11. unfold frame_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & L1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & L2 & _). rewrite L1, L2. reflexivity. }
assert (A2 : getr regs2 2 = w64 R).
{ rewrite <- (w7_r5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (w7_r5 (x_regs cx) 2%bv 2 eq_refl). exact P5. }
assert (A3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (w7_r5 regs2 3%bv 3 eq_refl). rewrite (Hr234 3 (or_intror (or_introl eq_refl))).
  rewrite (w7_r5 (x_regs cx) 3%bv 3 eq_refl). exact P6. }
assert (A4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (w7_r5 regs2 4%bv 4 eq_refl). rewrite (Hr234 4 (or_intror (or_intror eq_refl))).
  rewrite (w7_r5 (x_regs cx) 4%bv 4 eq_refl). exact P7. }
assert (AR_ : forall z v, In (LReg z, v) (rs_L_Dc0 rsegs cx sh np ps cnt es ++
    [(LReg 26, Z.of_nat (length r)); (LReg 22, F + 0xa0); (LReg 27, pb); (LReg 25, rs_cur rsegs cx rest r)]) ->
  getr regs2 (Z_to_bv 5 z) = w64 v) by (intros z v Hz; exact (w7_at_reg _ _ _ _ _ z v Hat Hz)).
assert (AC_ : forall o v, In (LCell XR o, v) (rs_L_Dc0 rsegs cx sh np ps cnt es ++
    [(LReg 26, Z.of_nat (length r)); (LReg 22, F + 0xa0); (LReg 27, pb); (LReg 25, rs_cur rsegs cx rest r)]) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (R + o) 8 (v mod 2 ^ 64)) by (intros o v Ho; exact (w7_at_cell _ _ _ _ _ o v Hat Ho)).
assert (G9 : getr regs2 9 = w64 R) by (rewrite <- (w7_r5 regs2 9%bv 9 eq_refl); apply AR_; w7_in).
assert (G18 : getr regs2 18 = w64 SHADOW_OFF) by (rewrite <- (w7_r5 regs2 18%bv 18 eq_refl); apply AR_; w7_in).
assert (G20 : getr regs2 20 = w64 (shadow_addr F)) by (rewrite <- (w7_r5 regs2 20%bv 20 eq_refl); apply AR_; w7_in).
assert (G21 : getr regs2 21 = w64 (F + 0x20)) by (rewrite <- (w7_r5 regs2 21%bv 21 eq_refl); apply AR_; w7_in).
assert (G22 : getr regs2 22 = w64 (F + 0xa0)) by (rewrite <- (w7_r5 regs2 22%bv 22 eq_refl); apply AR_; w7_in).
assert (G25 : getr regs2 25 = w64 (rs_cur rsegs cx rest r)) by (rewrite <- (w7_r5 regs2 25%bv 25 eq_refl); apply AR_; w7_in).
assert (G26 : getr regs2 26 = w64 (Z.of_nat (length r))) by (rewrite <- (w7_r5 regs2 26%bv 26 eq_refl); apply AR_; w7_in).
assert (G27 : getr regs2 27 = w64 pb) by (rewrite <- (w7_r5 regs2 27%bv 27 eq_refl); apply AR_; w7_in).
assert (Hpp63 : pp + Layout.PP_SIZE <= 2 ^ 63) by lia.
assert (C108 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x108) 8 (F + 0xf8)).
{ pose proof (AC_ 0x108 (F + 0xf8) ltac:(w7_in)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (C138 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x138) 8 (F + 0xf0)).
{ pose proof (AC_ 0x138 (F + 0xf0) ltac:(w7_in)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (Cc0 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xc0) 8 pp).
{ pose proof (AC_ 0xc0 pp ltac:(w7_in)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (Ce8 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xe8) 8 (shadow_addr (pp + 0x4000))).
{ pose proof (AC_ 0xe8 (shadow_addr (pp + 0x4000)) ltac:(w7_in)) as V. rewrite Z.mod_small in V; [exact V|].
  unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia)).
  assert ((pp + 0x4000) / 8 <= 2 ^ 63) by (apply Z.div_le_upper_bound; lia). lia. }
assert (Cb0 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xb0) 8 (pp + 0x4000)).
{ pose proof (AC_ 0xb0 (pp + 0x4000) ltac:(w7_in)) as V. rewrite Z.mod_small in V by lia. exact V. }
assert (C118 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x118) 8 ((-0x4001) mod 2 ^ 64)).
{ exact (AC_ 0x118 (-0x4001) ltac:(w7_in)). }
(* the read-only data and the shadow facts at G, from the segment's start *)
assert (KGimg : forall a, in_img rsegs a -> 0 <= a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha Ha0. destruct (E1img a Ha) as [N1 N2]. pose proof (w7_segs_low a Ha) as L. unfold kLowMemEnd in L.
  apply KG; [lia | exact N1 | exact N2]. }
assert (Img : forall a, 0x10000 <= a < 0x2f9d4 -> in_img rsegs a) by (intros a Ha; exact (w7_in_seg _ _ a w7_img_ro Ha)).
assert (Imgr : forall a, 0x9b690 <= a < 0x9d000 -> in_img rsegs a) by (intros a Ha; exact (w7_in_seg _ _ a w7_img_relro Ha)).
assert (Hp8 : 0 <= pb mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hpcell : val_mem rsegs (mrestrict (w_H W2) mem2) (W7_PTAB pb) 8 (w7_pptr (pb mod 8))).
{ unfold rt_ro_cells in Hcells. cbn [hi_cells rate_himg_A] in Hcells. rewrite Forall_forall in Hcells.
  pose proof (Hcells _ (w7_param_cell (pb mod 8) Hp8)) as V. cbn [fst snd] in V.
  refine (val_mem_kept rsegs (w_H (x_W cx)) (w_H W2) (x_memc cx) mem2 _ 8 _ _ V). intros i0 Hi0. unfold W7_PTAB.
  apply KGimg; [apply Imgr; lia | lia]. }
assert (Hpra : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (W7_PTAB pb) 8).
{ cbn [hi_globs rate_himg_A] in Hglobs. rewrite Forall_forall in Hglobs.
  assert (G : range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF 0x9bbe0 64)
    by (apply (Hglobs (0x9bbe0, 64)); cbv [rate_A_globs In]; repeat (first [left; reflexivity | right])).
  apply (range_addressable_sub _ _ 0x9bbe0 64 (W7_PTAB pb) 8) in G; [| unfold W7_PTAB; lia | unfold W7_PTAB; lia].
  apply (rtm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2); [exact G|].
  intros x Hx. destruct (E1sh x ltac:(unfold kHighMemEnd, W7_PTAB in *; lia) (NF _ _ G x Hx)) as [N1 N2].
  pose proof (rtm_shadow_band x ltac:(unfold kHighMemEnd, W7_PTAB in *; lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
  apply KG; [lia | exact N1 | exact N2]. }
assert (Hra160 : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (R + 0x160) 8).
{ cbn [hi_rz rate_himg_A] in Hrz. apply Forall_inv in Hrz. cbn [fst snd] in Hrz.
  apply (range_addressable_sub _ _ (R + 0x158) 16 (R + 0x160) 8) in Hrz; [| lia | lia].
  apply (rtm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2); [exact Hrz|].
  intros x Hx. destruct (E1sh x ltac:(unfold kHighMemEnd; lia) (NF _ _ Hrz x Hx)) as [N1 N2].
  pose proof (rtm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
  apply KG; [lia | exact N1 | exact N2]. }
assert (Strs : forall a s, In (a, s) rate_A_strs -> 0x10000 <= a -> a + Z.of_nat (length s) + 64 < 0x2f9d4 ->
  rt_cstr rsegs (w_H W2) mem2 a s).
{ intros a s Hs Ha1 Ha2. cbn [hi_strs rate_himg_A] in Hstrs. rewrite Forall_forall in Hstrs.
  pose proof (Hstrs (a, s) Hs) as C. cbn [fst snd] in C. pose proof C as (_ & _ & _ & _ & _ & _ & _ & Cra & _).
  apply (w7_cstr_tr _ _ (x_memc cx) mem2 a s C).
  - intros b Hb. apply KGimg; [apply Img; lia | lia].
  - intros x Hx. destruct (E1sh x ltac:(unfold kHighMemEnd; lia) (NF _ _ Cra x Hx)) as [N1 N2].
    pose proof (rtm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
    apply KG; [lia | exact N1 | exact N2].
  - intros y Hy Hv.
    assert (Hb : kLowMemEnd <= y < kHighMemBeg).
    { apply (w7_hull_band a (Z.of_nat (length s) + 1)); [lia | lia | unfold kHighMemEnd; lia | exact Hy]. }
    unfold kLowMemEnd, kHighMemBeg in Hb.
    destruct (Z_lt_le_dec y (shadow_addr F)) as [Hy1|Hy1];
    [| destruct (Z_lt_le_dec y (shadow_addr F + 56)) as [Hy2|Hy2]].
    + rewrite KG; [exact Hv | lia | lia |]. intros [Hw|Hp].
      * unfold rt_inw in Hw. cbn [hi_w1 rate_himg_A] in Hw.
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw;
          [fold e F in Hw; lia |].
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw; [fold e F in Hw; lia|].
        repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rt_xv] in Hw; fold e R in Hw; lia|]).
        apply Exists_nil in Hw. exact Hw.
      * fold e pp in Hp. rewrite HPS in Hp, P17'. lia.
    + unfold rs_fsh_at, rt_fsh in Hfsh. fold e F in Hfsh.
      pose proof (Hfsh (y - shadow_addr F) ltac:(change (length rs_PG) with 56%nat; lia)) as V.
      replace (shadow_addr F + (y - shadow_addr F)) with y in V by lia. rewrite V. discriminate.
    + rewrite KG; [exact Hv | lia | lia |]. intros [Hw|Hp].
      * unfold rt_inw in Hw. cbn [hi_w1 rate_himg_A] in Hw.
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw;
          [fold e F in Hw; lia |].
        apply Exists_cons in Hw as [Hw|Hw]; cbn [fst snd rt_xv] in Hw; [fold e F in Hw; lia|].
        repeat (apply Exists_cons in Hw as [Hw|Hw]; [cbn [fst snd rt_xv] in Hw; fold e R in Hw; lia|]).
        apply Exists_nil in Hw. exact Hw.
      * fold e pp in Hp. rewrite HPS in Hp, P17'. lia. }
assert (Hcs0 : rt_cstr rsegs (w_H W2) mem2 0x20fe0 (map (fun b : byte => bv_unsigned b) HPFX)).
{ apply Strs; [exact w7_hpfx_str | lia | rewrite length_map, w7_hpfx_len; simpl Z.of_nat; lia]. }
assert (Hcs2 : rt_cstr rsegs (w_H W2) mem2 (w7_sep pb) (map (fun b : byte => bv_unsigned b) (w7_sepb pb))).
{ pose proof (w7_sep_rng pb). pose proof (w7_sep_len pb). unfold w7_sepb in *.
  apply Strs; [exact (w7_sep_str pb) | lia | rewrite length_map; lia]. }
assert (Hcs3 : rt_cstr rsegs (w_H W2) mem2 (w7_pptr (pb mod 8)) (map (fun b : byte => bv_unsigned b) (w7_pab pb))).
{ pose proof (w7_pptr_rng (pb mod 8) Hp8). pose proof (w7_param_len pb). unfold w7_pab in *.
  apply Strs; [exact (w7_param_str (pb mod 8) Hp8) | lia | rewrite length_map; lia]. }
assert (Hro2 : aro_unowned rsegs B (aview rsegs (w_H W2) mem2)).
{ intros a Ha _ _. assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hs & _ & Hb); exists sg; split; [exact Hs | exact Hb]).
  pose proof (w7_segs_low a Hi) as L. unfold kLowMemEnd in L.
  rewrite KGimg by (first [exact Hi | lia]). exact (Hrom a Ha). }
(* ---- the walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs RS_G regs2 mem2 md2) with (mkCfg (mkst regs2 (Z_to_bv 64 0x8150c) mem2 (seg_rom rsegs)) md2).
  apply (w7_walk B LAWS ASTRLEN AMEMCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 (x_k cx) regs2 mem2 md2 R F (x_pos cx) (rs_cur rsegs cx rest r)
    (Z.of_nat (length r)) pb (pp + 0x4000) pp (shadow_addr (pp + 0x4000)) ((-0x4001) mod 2 ^ 64) chs);
  try assumption; try lia.
  - exact (w7_chs_nonzero rr chs pb r Hg).
  - unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia)).
    assert ((pp + 0x4000) / 8 <= 2 ^ 63) by (apply Z.div_le_upper_bound; lia). lia.
  - apply Z.mod_pos_bound. lia. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & J3 & Io3 & Kr3 & Km3 & Pr3 &
  (R27 & R22 & R25 & R23 & R24 & R26 & Re & Rsh)).
(* ---- the cut J ---- *)
assert (Wr_in : forall a, w7_WrW R F a -> (R - 16384 <= a < R) \/ rs_E1 rsegs cx a).
{ intros a Ha. unfold w7_WrW, ESTACK in Ha.
  destruct Ha as [X|[X|[X|[X|X]]]]; [left; lia | right; left | right; left | right; left | right; left];
  unfold rt_inw; cbn [hi_w1 rate_himg_A].
  - do 5 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. fold e R. lia.
  - apply Exists_cons_hd. cbn [fst snd rt_xv]. fold e F. lia.
  - apply Exists_cons_hd. cbn [fst snd rt_xv]. fold e F. lia.
  - apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. fold e F. lia. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ w7_WrW R F a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a)
  by exact Km3.
assert (Kr3' : forall z, 0 < z < 32 -> ~ In (Z_to_bv 5 z) (w7_clobW) ->
  getr regs3 (Z_to_bv 5 z) = getr regs2 (Z_to_bv 5 z)).
{ intros z Hz Hn. apply Kr3; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32;
  rewrite Z.mod_small by lia; lia | exact Hn]. }
apply (HJc ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es rr r (ent_text (w7_js chs pb) true) Hlen Hles).
split.
- (* rs_pod_base *)
  split; [|exact (proj2 Hbase)].
  split; [exact J3|]. split.
  { intros z Hz. rewrite <- (Hr234 z Hz). apply Kr3'; [destruct Hz as [-> | [-> | -> ]]; lia|].
    destruct Hz as [-> | [-> | -> ]]; unfold w7_clobW; cbv [rts_caller_saved app In]; intros X;
    repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X|]); exact X. }
  split; [exact Hfr2|]. split; [exact Hperm2|]. split; [exact (same_io_trans _ _ _ Hio2 Io3)|]. split; [exact Hmo2|].
  intros a Ha H1 H2. rewrite Hsp in H1. rewrite K3; [| exact Ha |].
  + apply Hmem2; [exact Ha | rewrite Hsp; exact H1 | exact H2].
  + intros X. destruct (Wr_in a X) as [Y|Y]; [unfold T_SEG_STK, ASTACK in H1; lia | exact (H2 Y)].
- split.
  { (* the (location, value) facts *)
    unfold rs_at_cx, rs_at. fold e.
    assert (Kc : forall o v, In (LCell XR o, v) (rs_L_Dc0 rsegs cx sh np ps cnt es ++
        [(LReg 26, Z.of_nat (length r)); (LReg 22, F + 0xa0); (LReg 27, pb); (LReg 25, rs_cur rsegs cx rest r)]) ->
      0x10 <= o -> o + 8 <= 0x140 -> rt_at rsegs (w_H W2) mem3 regs3 e (LCell XR o) v).
    { intros o v Ho Ho1 Ho2. apply (rtm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 e (LCell XR o) v
        (proj1 (Forall_forall _ _) Hat _ Ho)).
      cbn [rtm_keeps rt_xv]. fold R. intros i0 Hi0. apply K3; [lia|]. unfold w7_WrW, ESTACK.
      unfold in_app in FA. unfold T_SEG_STK, ASTACK in P8. lia. }
    cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_Hc rs_podc app].
    repeat apply Forall_cons; cbn [fst snd].
    all: first
      [ apply Forall_nil
      | (apply Kc; [w7_in | lia | lia])
      | (lazymatch goal with |- rt_at _ _ _ _ _ ?l ?v =>
           apply (rtm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 e l v
           (proj1 (Forall_forall _ _) Hat (l, v) ltac:(w7_in))) end;
         cbn [rtm_keeps]; apply Kr3'; [lia | unfold w7_clobW; cbv [rts_caller_saved app In];
         let X := fresh "X" in intros X;
         repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X|]);
         exact X])
      | (cbn [rt_at]; rewrite (w7_r5 regs3 27%bv 27 eq_refl); exact R27)
      | (cbn [rt_at]; rewrite (w7_r5 regs3 22%bv 22 eq_refl); exact R22)
      | (cbn [rt_at]; rewrite (w7_r5 regs3 25%bv 25 eq_refl); exact R25)
      | (cbn [rt_at]; rewrite (w7_r5 regs3 24%bv 24 eq_refl); exact R24)
      | (cbn [rt_at]; rewrite (w7_r5 regs3 23%bv 23 eq_refl); exact R23)
      | (cbn [rt_at]; rewrite (w7_r5 regs3 26%bv 26 eq_refl), R26; apply Z_to_bv_mod64) ].
    }
  split; [exact Rsh|].
  split.
  { (* the first block's image: pp is no byte the walk writes *)
    assert (Hent : (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\
      Forall (fun e0 => (length (e_body e0) <= 96)%nat) (pc_ents (PbCut sh ps (Some es)))).
    { exact (w7_pc_ents_ok sh ps es Hwf Hesw ltac:(lia)). }
    destruct Hwf as (_ & Hkv & Hae & _).
    assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hkv]; intros kv [_ X]; exact X).
    destruct (pc_buf_len_open sh ps es Hpv Hae Hesw) as [Hbl _].
    assert (Hlimg : Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE).
    { unfold pc_image. apply length_pp_image; [lia | exact (proj1 Hent) | exact (proj2 Hent)]. }
    pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HARc P14 P12) as Hsep.
    rewrite <- P11 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    change (req_size Layout.PP_SIZE) with 19744 in Hsep. change (fs_frame_bytes 3) with 512 in Hsep.
    unfold rs_pp_at. apply (rtm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) mem3); [exact Hpp|].
    intros x Hx. rewrite Hlimg, HPS in Hx. fold e pp in Hx. apply K3; [lia|].
    unfold w7_WrW, ESTACK. rewrite HPS in P16, P17'. unfold T_SEG_STK, ASTACK in P8.
    assert (Hb : 0x7fff8000 <= shadow_addr F /\ shadow_addr F + 64 <= 0x10007fff8000).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia)).
      assert (F / 8 <= 2 ^ 44 - 64) by (apply Z.div_le_upper_bound; lia). lia. }
    lia. }
  split; [exact Re|].
  split; [symmetry; exact (w7_ent_build_0 rr chs pb r Hk0 Hg Hchs)|].
  rewrite (w7_ent_text_js chs pb Hchs). unfold ent_wf. cbn [e_type e_size e_body].
  pose proof (w7_js_len chs pb Hchs) as Hjs. unfold POD_STRING.
  rewrite length_app. cbn [length]. split; [lia|]. split; [lia|]. lia.
Qed.
End b.

Print Assumptions w7_piece.
