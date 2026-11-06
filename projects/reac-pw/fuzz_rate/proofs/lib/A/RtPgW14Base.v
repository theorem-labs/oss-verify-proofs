(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 1d255703e887 (the shared layer
   of the match half of fuzz_role's image-A segment M02) for reac-pw/fuzz_rate image A: role's pcs become rate's, the
   code table covers rate's four blocks (the key compare, the two readers, the two checks and their five slow
   blocks), the shadow base moves from role's s7 to rate's s2 (atom 18), the frame cell the half reads is rate's hz
   cell at F+0x180 held in s5 (atom 21) instead of role's role cell in s6, the real frame's size is 0x1e0, the
   quantity record is rate's rt_renv (q_ instead of e_) and the callee seam is stated over rate's rt_cpost_g, so a
   callee that keeps the caller's owned set (lib/A/RtPgCSpec.v rt_cpost_o) uses it too. Role's string lemma m2_strs
   is replaced by m2_key_at: rate's match half calls only check_absent / check_rate / check_malformed (no string
   premise), pod_nearest (rom_view) and the strcmp wrapper against the harness's own key at 0x20fa0, so one string
   is carried, not ten. The generic plumbing role's file takes from its lib/A/RPgCheck.v (the entry state's register
   overrides, the kept-run lemma and the write-range tactics) is taken here from lib/A/RtPgCheck.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Base.v, with its addresses changed; 91 of its 162 lines of code are new or changed and 339 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, which holds the same loaded bytes): what the two
   W14 pieces of segment M02 share, the asked[] set-up (A 0x82ca8 -> DEC 0x82d14, lib/A/RtPgW14Ask.v) and the loop's
   tail (T2 0x82e74 -> C4 0x82e84, lib/A/RtPgW14Tail.v). Proves no function (kind: segment lemma).
   - w14_tbl: the 31 4-byte words the two runs read (0x82ca8 .. 0x82d10 and 0x82e74 .. 0x82e80). No instrumented
     check lies in either range, so w14_run is the plain engine (YCbq aj_run); w14_r234 / w14_sp234 carry sp, gp, tp.
   - w14_tz: the two 8-byte tables reac_rate_refuse_code.codes (0x9bc80) and switch.table.check_code (0x9bc40) in the
     first writable segment, and their shadow bytes: no byte of it is in M02's write set or in the callees' stack
     (w14_tz_ok), so the tables read the same at every cut (w14_u64_kept).
   - w14_strs: the strings and tables check_code and reac_rate_refuse_code read (RtPgSiteA.rate_A_site_strs at the
     segment's start), at a cut's memory: the strings through RtPgM02Base.m2_cstr_kept, the tables through
     w14_u64_kept.
   The seam with the callee contracts, the stack and frame facts and the entry state are RtPgM02Base.v's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSiteA RtPgSeg RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCheck RtPgM02Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================= the image ======================================= *)
Definition W14_A : Z := 0x82ca8.
Definition W14_DEC : Z := 0x82d14.
Definition W14_T2 : Z := 0x82e74.
Definition W14_T2R : Z := 0x82e7c.          (* reac_rate_refuse_code's return address *)
Definition W14_C4 : Z := 0x82e84.
Definition W14_REFUSE : Z := 0x83f60.       (* reac_rate_refuse_code *)
Definition W14_CODE : Z := 0x83734.         (* check_code *)
Definition W14_RF_TBL : Z := 0x9bc80.       (* reac_rate_refuse_code.codes *)
Definition W14_RF_COV : Z := 0x21600.
Definition W14_RF_CS : list Z := [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Definition W14_CC_TBL : Z := 0x9bc40.       (* switch.table.check_code *)
Definition W14_CC_LNONE : Z := 0x215c0.
Definition W14_CC_CS : list Z := [0x21540; 0x21560; 0x21580; 0x215a0].

(* the 27 words 0x82ca8 .. 0x82d10 (the asked[] set-up) and the 4 words 0x82e74 .. 0x82e80 (the tail) *)
Definition w14_tbl : ctable := Eval vm_compute in (build_table rsegs W14_A 27 (build_table rsegs W14_T2 4 TEmpty)).
Lemma w14_tbl_eq : w14_tbl = build_table rsegs W14_A 27 (build_table rsegs W14_T2 4 TEmpty).
Proof. vm_cast_no_check (eq_refl w14_tbl). Qed.
Lemma w14_tbl_ok : table_ok rsegs w14_tbl.
Proof.
rewrite w14_tbl_eq. apply build_table_ok; [unfold W14_A; lia|]. apply build_table_ok0. unfold W14_T2. lia.
Qed.
Lemma w14_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma w14_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact ck_segs_low. Qed.

(* No instrumented check lies in either range, so the runs are the plain engine's (YCbq aj_run): no shadow entry
   and no static shadow check; the frame's shadow bytes the set-up stores are a region like any other. *)
Ltac w14_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
aj_run w14_tbl_ok HS HJ; [awr | ] end.

(* sp / gp / tp kept by a run that leaves their atoms in place *)
Lemma w14_r234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Proof.
intros r1 r2 H r Hr; destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma w14_sp234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. apply (m2_sp_of_cs [2; 3; 4]%bv r1 r2); [cbv [In]; left; reflexivity | exact H]. Qed.

(* ======================================= the two tables ======================================= *)
Definition w14_tz (a : Z) : Prop :=
(0x9b800 <= a < 0x9c000) \/ (SHADOW_OFF + 0x13700 <= a < SHADOW_OFF + 0x13800).

(* [0x9b800, 0x9c000) lies inside image A's first writable PT_LOAD [0x9b690, 0x9d000) *)
Lemma w14_tz_img : forall a, 0x9b800 <= a < 0x9c000 -> in_img rsegs a.
Proof.
intros a Ha.
assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x9b800) &&
  (0x9c000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
exists sg. split; [exact Hin | lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* No byte of the zone is in M02's write set or in the callees' stack: its image bytes by m2_keep_img; a shadow
   byte of it at shadow_addr F + c (c = 0x30, 0x32, 0x34) would put F + 8 c, a byte of F, in the image. *)
Lemma w14_tz_ok : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, w14_tz a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rs_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a [Ha|Ha]; [exact (m2_keep_img B cx Hpre Hpod a (w14_tz_img a Ha))|].
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack B cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
assert (HF8 : q_F (x_e rsegs cx) = 8 * (q_F (x_e rsegs cx) / 8)).
{ pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
  assert (q_F (x_e rsegs cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; lia); rewrite F32; reflexivity).
  lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
rewrite HR. unfold T_SEG_STK, ASTACK. unfold SHADOW_OFF in Ha.
split; [lia|]. split; [lia|].
unfold rs_E2, rt_inw. cbn [hi_w2 rate_himg_A]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]]]]];
  try unfold shadow_addr in Hw; try unfold SHADOW_OFF in Hw;
  first
  [ lia
  | (apply (Fimg (q_F (x_e rsegs cx) + 0x180)); [lia | apply w14_tz_img; lia])
  | (apply (Fimg (q_F (x_e rsegs cx) + 0x190)); [lia | apply w14_tz_img; lia])
  | (apply (Fimg (q_F (x_e rsegs cx) + 0x1a0)); [lia | apply w14_tz_img; lia]) ].
- lia.
Qed.
End d.

(* a table of the zone whose bytes and shadow bytes read the same in another world and memory is the same table *)
Lemma w14_u64_kept : forall H H' (m m' : word -> option byte) t vs,
(forall x, w14_tz x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x9b800 <= t -> t + 8 * Z.of_nat (length vs) <= 0x9c000 ->
rt_u64tab rsegs H m t vs -> rt_u64tab rsegs H' m' t vs.
Proof.
intros H H' m m' t vs HK Ht Hb (Himg & Hal & Hvs & Hv & Hra).
split; [exact Himg|]. split; [exact Hal|]. split; [exact Hvs|].
split.
- intros i Hi. eapply (val_mem_kept rsegs); [|exact (Hv i Hi)]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply HK. left. lia.
- apply (rtm_ra_kept rsegs H m H' m'); [exact Hra|]. intros x Hx. apply HK. right.
  unfold shadow_of_addr, SHADOW_OFF.
  assert (0x13700 <= x / 8 < 0x13800) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia.
Qed.

Section d2.
Variable B : asyms.
Variable MT : ameter_ops.

(* the premises reac_rate_refuse_code and check_code read, at a cut's memory *)
Lemma w14_strs : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rt_u64tab rsegs (w_H W2) mem2 W14_RF_TBL W14_RF_CS /\
rt_u64tab rsegs (w_H W2) mem2 W14_CC_TBL W14_CC_CS /\
(forall i, 0 <= i < 4 -> rt_cstr rsegs (w_H W2) mem2 (nth (Z.to_nat i) W14_CC_CS 0) (rt_code_of_txt (i + 1))) /\
rt_cstr rsegs (w_H W2) mem2 W14_CC_LNONE (rt_code_of_txt 0) /\
rt_cstr rsegs (w_H W2) mem2 0x21680 (rt_refuse_txt 4).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
assert (HK : forall x, m2_kz x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (m2_kz_ok B cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
assert (HT : forall x, w14_tz x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (w14_tz_ok B cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
pose proof Hpre as Hpre'. unfold rs_pre in Hpre'.
destruct (rate_A_site_strs rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre')
as (SC & SN & SR & _ & _ & _ & _ & _ & _ & _ & _ & UC & UR).
split; [apply (w14_u64_kept _ _ _ _ _ _ HT);
  [unfold W14_RF_TBL; lia | unfold W14_RF_TBL, W14_RF_CS; simpl; lia | exact UR]|].
split; [apply (w14_u64_kept _ _ _ _ _ _ HT);
  [unfold W14_CC_TBL; lia | unfold W14_CC_TBL, W14_CC_CS; simpl; lia | exact UC]|].
split.
{ intros i Hi. specialize (SC i Hi). unfold W14_CC_CS.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
  destruct C as [->|[->|[->| ->]]];
  (apply (m2_cstr_kept _ _ _ _ _ _ HK); [vm_compute; congruence | vm_compute; reflexivity | exact SC]). }
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [vm_compute; congruence | vm_compute; reflexivity | exact SN]|].
specialize (SR 4 ltac:(lia)). change (rt_refuse [0x21600; 0x21620; 0x21640; 0x21660; 0x21680] 0x21600 4) with 0x21680 in SR.
apply (m2_cstr_kept _ _ _ _ _ _ HK); [vm_compute; congruence | vm_compute; reflexivity | exact SR].
Qed.
End d2.
End b.

Print Assumptions w14_tz_ok.
Print Assumptions w14_strs.
