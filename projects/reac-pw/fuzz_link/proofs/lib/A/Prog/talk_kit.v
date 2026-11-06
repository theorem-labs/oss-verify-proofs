(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 576 of its 626 lines of code are new or changed and 259 lines of the source are left out. *)
(* talk on image A: the steps every part file of its walk takes (lib/A/Prog/talk_defs.v names the states, the
   invariant and the pieces).
   - tk_sp_bounds, tk_sp_rng, tk_aarg_rng, tk_m_facts, tk_r_facts, tk_kd_facts, tk_ad_facts, tk_ewr_facts: what the
     call's premises (tk_call) say of the frame, the model block, the request, the two buffers and the write set;
   - tk_E_reg, tk_E_ext, tk_E_xs, tk_E_env, tk_E_gnl: the atoms of a fresh symbolic state;
   - tk_regs_ok_ovr, tk_den_of_U, tk_den_shx, tk_ov_ch_ok, tk_ov_at_ok, tk_ov_c1_ok: the overridden registers;
   - tk_fr_ok, tk_frw_ok, tk_frs_ok: the three frame regions (saved words, spill area, spilled words);
   - tk_st_ok: THE STATE BUILDER, a fresh state `tk_ss pc ov rs ex` at a machine state that satisfies tk_inv;
   - tk_shadow_kept, tk_ra_kept, tk_hull_kept, tk_gnl_kept, tk_nlk_kept, tk_gnl_val, tk_shent_ok: the shadow
     transfers (a range_addressable / shadow_hull_vis of the call's memory holds at the current memory, g_nl keeps
     its bytes, an SH entry from a range_addressable);
   - tk_inv_step: the invariant across a run that writes only below the saved words or the write set;
   - tk_preserved, tk_intrin: the step through checked_memcpy whose destination lies in the model block or a live
     buffer (dest_ok's `~ aowned` from apre's ajw, as lib/A/Prog/fuzz_recv_kit2.v), tk_src_gnl / tk_src_req: its
     source premises for a source in g_nl's chunk queue or the request.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_kit talk_c talk_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ---- generic: overridden registers, 8-byte chunks, denotations ---------------------------------------------- *)
Lemma tk_regs_ok_set : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e Hr He r'. specialize (Hr r'). unfold sr_set.
  destruct (bv_eqb r 0) eqn:Hr0; [exact Hr|].
  unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
  rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
  apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact He.
Qed.

Lemma tk_regs_ok_ovr : forall E regs ov sr,
  regs_ok E sr regs -> Forall (fun p => sv_denot E (snd p) = getr regs (fst p)) ov -> regs_ok E (tk_ovr ov sr) regs.
Proof.
  intros E regs ov. induction ov as [|[r v] ov IH]; intros sr Hsr Hov; cbn [tk_ovr]; [exact Hsr|].
  apply Forall_cons_iff in Hov as [Hv Hov]. cbn [fst snd] in Hv.
  apply IH; [apply tk_regs_ok_set; [exact Hsr | exact Hv] | exact Hov].
Qed.

Lemma tk_den_of_U : forall E v z, U E v = z -> sv_denot E v = w64 z.
Proof. intros E v z H. rewrite denot_lit_U, H. reflexivity. Qed.

Lemma tk_U_shx : forall E v x, U E v = x -> U E tk_Bx = SHADOW_OFF -> 0 <= x < 2 ^ 64 ->
  U E (tk_shx_sv v) = tk_shx x.
Proof.
  intros E v x Hv HB Hx. unfold tk_shx_sv. rewrite !U_SAlu, Hv, HB, U_lit by lia. cbn [zalu_raw].
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64, tk_shx.
  assert (Hd : 0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (x / 8)) by lia. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

Lemma tk_den_shx : forall E v x, U E v = x -> U E tk_Bx = SHADOW_OFF -> 0 <= x < 2 ^ 64 ->
  sv_denot E (tk_shx_sv v) = w64 (tk_shx x).
Proof. intros E v x Hv HB Hx. apply tk_den_of_U. exact (tk_U_shx E v x Hv HB Hx). Qed.


(* an 8-byte chunk of a region from the val_mem of its word *)
Lemma tk_chunk8 : forall E m base o n k (w : word),
  val_mem SEGS m (base + o) 8 (bv_unsigned w) -> sv_denot E (SOff n k) = w ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk o (CVal 8 (SOff n k))).
Proof.
  intros E m base o n k w Hv Hd.
  apply (chunk_ok_val SEGS E m base o 8 (SOff n k) (bv_unsigned w)).
  - rewrite Hd. symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - exact Hv.
Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation mbs := (tc_mbs c).
#[local] Notation kbs := (tc_kbs c).

(* ---- the call's premises -------------------------------------------------------------------------------------- *)
Lemma tk_aarg_rng : forall i, 0 <= aarg regs0 i < 2 ^ 64.
Proof.
  intros i. unfold aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (10 + i)))) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

(* the frame [tk_sp - 144, tk_sp) and the callee's window below it lie in the journal's window, above the ceiling *)
Lemma tk_sp_bounds :
  alloc_ceiling <= tc_sp0 c - tc_STK c /\ tc_sp0 c - tc_STK c <= tk_sp c - TALK_AK /\ tk_sp c <= tc_sp0 c /\
  tc_sp0 c + tc_XO c <= 2 ^ 47 /\ tk_sp c mod 16 = 0 /\ 0 <= tc_XO c.
Proof.
  destruct HC as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hwlo & Hwhi & _) & _).
  destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold tk_sp. lia.
Qed.

Lemma tk_sp_rng : 2 ^ 46 <= tk_sp c - 144 /\ tk_sp c <= 2 ^ 47 /\ (tk_sp c - 144) mod 16 = 0 /\
  alloc_ceiling + 4096 <= tk_sp c - 144.
Proof.
  destruct tk_sp_bounds as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold TALK_AK, TALK_AFRAME, ESTACK in Hlo. lia.
Qed.

Ltac tk_HC := pose proof HC as (HA & HMD & HMW & HNK & HNW & HRQ & HRL & HLEN & HBK & HBA & HRAm & HHm & HAMm &
  HRAq & HHq & HAMr & HRAr & HHr & HAPrm & HKD & HAD & HKA & HGm & HFm & HFr & HFk & HFa).

Lemma tk_m_facts :
  0 <= tk_m c /\ tk_m c + MD_SIZE <= kHighMemEnd - 1 /\ amem_range (tk_m c) MD_SIZE /\
  apart_gnl LA_G_NL (tk_m c) MD_SIZE /\ apart_frame regs0 TALK_AK (tk_m c) MD_SIZE /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (tk_m c) MD_SIZE /\
  shadow_hull_vis (aview SEGS (w_H W) memc) (tk_m c) MD_SIZE /\ amodel_at SEGS (rdW W memc) (tk_m c) mbs.
Proof.
  tk_HC. pose proof (tk_aarg_rng 0) as R0. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold tk_m. refine (conj (proj1 R0) (conj _ (conj HAMm (conj HGm (conj HFm (conj HRAm (conj HHm HMD))))))).
  unfold amem_range in HAMm. destruct HAMm as [Hq|Hq]; lia.
Qed.

Lemma tk_r_facts :
  0 <= tk_r c /\ 0 <= tk_len c <= NL_SENT_LEN /\ amem_range (tk_r c) (tk_len c) /\
  tk_r c + tk_len c <= kHighMemEnd - 1 /\
  apart_frame regs0 TALK_AK (tk_r c) (tk_len c) /\ apart (tk_r c) (tk_len c) (tk_m c) MD_SIZE /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (tk_r c) (tk_len c) /\
  (0 < tk_len c -> shadow_hull_vis (aview SEGS (w_H W) memc) (tk_r c) (tk_len c)) /\
  abytes SEGS (rdW W memc) (tk_r c) (tc_req c) /\ Z.of_nat (length (tc_req c)) = tk_len c.
Proof.
  tk_HC. pose proof (tk_aarg_rng 1) as R1. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold tk_r, tk_len, tk_m. refine (conj (proj1 R1) (conj HLEN (conj HAMr (conj _ (conj HFr (conj HAPrm
    (conj HRAr (conj HHr (conj HRQ HRL))))))))).
  unfold amem_range in HAMr. destruct HAMr as [Hq|Hq]; lia.
Qed.

Lemma tk_kd_facts : tk_kd c <> 0 -> 1 <= tk_kn c ->
  0 < tk_kd c /\ tk_kd c + tk_kn c <= kHighMemEnd - 1 /\ amem_range (tk_kd c) (tk_kn c) /\
  apart_gnl LA_G_NL (tk_kd c) (tk_kn c) /\ apart (tk_kd c) (tk_kn c) (tk_m c) MD_SIZE /\
  apart_frame regs0 TALK_AK (tk_kd c) (tk_kn c) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (tk_kd c) (tk_kn c) /\
  shadow_hull_vis (aview SEGS (w_H W) memc) (tk_kd c) (tk_kn c) /\ abuf SEGS (rdW W memc) (tk_kd c) (tk_kn c).
Proof.
  intros H0 H1. tk_HC. pose proof (tk_aarg_rng 3) as R3. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold tk_kd, tk_kn, tk_m in *.
  destruct (HKD H0 H1) as (G & Am & Ar & Ra & Hh). pose proof (HFk H0) as Fr. pose proof (HBK H0 H1) as Bf.
  refine (conj _ (conj _ (conj Ar (conj G (conj Am (conj Fr (conj Ra (conj Hh Bf)))))))); [lia|].
  unfold amem_range in Ar. destruct Ar as [Hq|Hq]; lia.
Qed.

Lemma tk_ad_facts : tk_ad c <> 0 -> 1 <= tk_an c ->
  0 < tk_ad c /\ tk_ad c + tk_an c <= kHighMemEnd - 1 /\ amem_range (tk_ad c) (tk_an c) /\
  apart_gnl LA_G_NL (tk_ad c) (tk_an c) /\ apart (tk_ad c) (tk_an c) (tk_m c) MD_SIZE /\
  apart_frame regs0 TALK_AK (tk_ad c) (tk_an c) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (tk_ad c) (tk_an c) /\
  shadow_hull_vis (aview SEGS (w_H W) memc) (tk_ad c) (tk_an c) /\ abuf SEGS (rdW W memc) (tk_ad c) (tk_an c).
Proof.
  intros H0 H1. tk_HC. pose proof (tk_aarg_rng 5) as R5. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold tk_ad, tk_an, tk_m in *.
  destruct (HAD H0 H1) as (G & Am & Ar & Ra & Hh). pose proof (HFa H0) as Fr. pose proof (HBA H0 H1) as Bf.
  refine (conj _ (conj _ (conj Ar (conj G (conj Am (conj Fr (conj Ra (conj Hh Bf)))))))); [lia|].
  unfold amem_range in Ar. destruct Ar as [Hq|Hq]; lia.
Qed.

Lemma tk_kd_ad_apart : tk_kd c <> 0 -> 1 <= tk_kn c -> tk_ad c <> 0 -> 1 <= tk_an c ->
  apart (tk_kd c) (tk_kn c) (tk_ad c) (tk_an c).
Proof. intros H0 H1 H2 H3. tk_HC. exact (HKA H0 H1 H2 H3). Qed.

(* a byte of the write set: outside the frame window and g_nl, in low or high memory *)
Lemma tk_ewr_facts : forall a, tk_ewr c a ->
  ~ (tk_sp c - TALK_AK <= a < tk_sp c) /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE) /\
  ((0 <= a /\ a < kLowMemEnd - 1) \/ (kHighMemBeg <= a /\ a < kHighMemEnd - 1)).
Proof.
  intros a ((lo, hi) & Hin & Hx). unfold talk_awr in Hin. cbn [In] in Hin. cbn [fst snd] in Hx.
  destruct tk_m_facts as (Hm0 & Hm1 & Hm2 & Hm3 & Hm4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hin as [Hq | [Hq | [Hq | []]]].
  - injection Hq as <- <-. unfold tk_m, tk_sp, apart_frame, apart_gnl, amem_range, NK_SIZE, LA_G_NL in *.
    destruct Hm2 as [Hq|Hq]; lia.
  - unfold aivl in Hq. injection Hq as <- <-. pose proof (tk_aarg_rng 4) as R4. revert Hx.
    destruct (Z.eqb_spec (aarg regs0 3) 0) as [E0|E0]; intros Hx; [lia|].
    destruct (Z.le_gt_cases 1 (aarg regs0 4)) as [E1|E1]; [|lia].
    destruct (tk_kd_facts E0 E1) as (K0 & K1 & K2 & K3 & _ & K5 & _).
    unfold tk_kd, tk_kn, tk_sp, apart_frame, apart_gnl, amem_range, NK_SIZE, LA_G_NL in *.
    destruct K2 as [Hq|Hq]; lia.
  - unfold aivl in Hq. injection Hq as <- <-. pose proof (tk_aarg_rng 6) as R6. revert Hx.
    destruct (Z.eqb_spec (aarg regs0 5) 0) as [E0|E0]; intros Hx; [lia|].
    destruct (Z.le_gt_cases 1 (aarg regs0 6)) as [E1|E1]; [|lia].
    destruct (tk_ad_facts E0 E1) as (K0 & K1 & K2 & K3 & _ & K5 & _).
    unfold tk_ad, tk_an, tk_sp, apart_frame, apart_gnl, amem_range, NK_SIZE, LA_G_NL in *.
    destruct K2 as [Hq|Hq]; lia.
Qed.

(* the destination of a checked_memcpy: a sub-range of the model block or of a live buffer *)
Definition tk_dst (d n : Z) : Prop :=
  (tk_m c <= d /\ d + n <= tk_m c + MD_SIZE) \/
  (tk_kd c <> 0 /\ 1 <= tk_kn c /\ tk_kd c <= d /\ d + n <= tk_kd c + tk_kn c) \/
  (tk_ad c <> 0 /\ 1 <= tk_an c /\ tk_ad c <= d /\ d + n <= tk_ad c + tk_an c).

Lemma tk_dst_facts : forall d n, tk_dst d n -> 0 <= n ->
  0 <= d /\ d + n <= kHighMemEnd - 1 /\ amem_range d n /\ apart_frame regs0 TALK_AK d n /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF d n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memc) d n) /\
  (forall a, d <= a < d + n -> tk_ewr c a /\ writable_at SEGS (rdW W memc) a).
Proof.
  intros d n Hd Hn.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hd as [(D0 & D1) | [(E0 & E1 & D0 & D1) | (E0 & E1 & D0 & D1)]].
  - destruct tk_m_facts as (Hm0 & Hm1 & Hm2 & Hm3 & Hm4 & Hm5 & Hm6 & ((_ & Hwr) & HL)).
    split; [lia|]. split; [lia|]. split; [unfold amem_range in *; destruct Hm2; lia|].
    split; [unfold apart_frame in *; lia|].
    split; [apply (range_addressable_sub _ _ (tk_m c) MD_SIZE); [exact Hm5 | lia | lia]|].
    split; [intros Hn0; apply (rv_hull_sub _ (tk_m c) MD_SIZE); [exact Hm6 | lia | lia | exact Hn0]|].
    intros a Ha. split.
    + unfold tk_ewr, inFP. exists (aarg regs0 0, aarg regs0 0 + MD_SIZE).
      split; [unfold talk_awr; cbn [In]; left; reflexivity|].
      cbn [fst snd]. unfold tk_m in *. lia.
    + replace a with (tk_m c + (a - tk_m c)) by lia. apply Hwr. rewrite HL. lia.
  - destruct (tk_kd_facts E0 E1) as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & (junk & Hjl & (_ & Hwr))).
    split; [lia|]. split; [lia|]. split; [unfold amem_range in *; destruct K2; lia|].
    split; [unfold apart_frame in *; lia|].
    split; [apply (range_addressable_sub _ _ (tk_kd c) (tk_kn c)); [exact K6 | lia | lia]|].
    split; [intros Hn0; apply (rv_hull_sub _ (tk_kd c) (tk_kn c)); [exact K7 | lia | lia | exact Hn0]|].
    intros a Ha. split.
    + unfold tk_ewr, inFP. exists (aivl (aarg regs0 3) (aarg regs0 4)).
      split; [unfold talk_awr; cbn [In]; right; left; reflexivity|].
      unfold aivl. unfold tk_kd, tk_kn in *. rewrite (proj2 (Z.eqb_neq _ _) E0). cbn [fst snd]. lia.
    + replace a with (tk_kd c + (a - tk_kd c)) by lia. apply Hwr. rewrite Hjl. lia.
  - destruct (tk_ad_facts E0 E1) as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & (junk & Hjl & (_ & Hwr))).
    split; [lia|]. split; [lia|]. split; [unfold amem_range in *; destruct K2; lia|].
    split; [unfold apart_frame in *; lia|].
    split; [apply (range_addressable_sub _ _ (tk_ad c) (tk_an c)); [exact K6 | lia | lia]|].
    split; [intros Hn0; apply (rv_hull_sub _ (tk_ad c) (tk_an c)); [exact K7 | lia | lia | exact Hn0]|].
    intros a Ha. split.
    + unfold tk_ewr, inFP. exists (aivl (aarg regs0 5) (aarg regs0 6)).
      split; [unfold talk_awr; cbn [In]; right; right; left; reflexivity|].
      unfold aivl. unfold tk_ad, tk_an in *. rewrite (proj2 (Z.eqb_neq _ _) E0). cbn [fst snd]. lia.
    + replace a with (tk_ad c + (a - tk_ad c)) by lia. apply Hwr. rewrite Hjl. lia.
Qed.

(* ---- the atoms of a fresh symbolic state ---------------------------------------------------------------------- *)
Lemma tk_E_reg : forall regs xs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (tk_E c regs xs) n = getr regs r.
Proof.
  intros regs xs n r Hn Hr. unfold tk_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hr).
Qed.

Lemma tk_E_ext : forall regs xs j, (j < 17)%nat -> ew (tk_E c regs xs) (32 + j) = nth j (tk_ext c) (Z_to_bv 64 0).
Proof.
  intros regs xs j Hj. unfold tk_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  apply app_nth1. unfold tk_ext. cbn [length]. lia.
Qed.

Lemma tk_E_xs : forall regs xs j, (j < 191)%nat -> ew (tk_E c regs xs) (49 + j) = nth j xs (Z_to_bv 64 0).
Proof.
  intros regs xs j Hj. unfold tk_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (49 + j)%nat with (32 + (17 + j))%nat by lia. rewrite ew_Ereg_extra.
  rewrite app_nth2 by (unfold tk_ext; cbn [length]; lia). f_equal. unfold tk_ext. cbn [length]. lia.
Qed.

Lemma tk_E_env : forall regs xs, img_env VAL A_LIM (tk_E c regs xs).
Proof. intros regs xs. unfold tk_E. apply Eimg_env. Qed.

Lemma tk_E_gnl : forall regs xs, bv_unsigned (ew (tk_E c regs xs) (A_OBJ 2)) = LA_G_NL.
Proof.
  intros regs xs. rewrite (tk_E_env regs xs (A_OBJ 2)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (lv_obj LV 2) by (unfold link_nobj; lia). reflexivity.
Qed.

(* an atom that is a register: its U value *)
Lemma tk_U_reg : forall regs xs n (r : bv 5) v, (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> U (tk_E c regs xs) (SOff n 0) = v.
Proof.
  intros regs xs n r v Hn Hr Hv Hv0. apply U_atom; [|exact Hv0]. rewrite (tk_E_reg regs xs n r Hn Hr). exact Hv.
Qed.

(* ---- the overridden registers of the stages -------------------------------------------------------------------- *)
Lemma tk_ov_ch_ok : forall regs xs, tk_rch c regs -> getr regs 23 = w64 SHADOW_OFF ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) tk_ov_ch.
Proof.
  intros regs xs (R10 & R13 & R14 & R15 & R16 & R17 & R6) R23.
  destruct tk_m_facts as (Hm0 & Hm1 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold tk_ov_ch. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite R13. apply tk_den_shx.
    + apply (tk_U_reg regs xs 10 10%bv); [lia | reflexivity | exact R10 | unfold MD_NEXT, MD_SIZE in *; lia].
    + apply (tk_U_reg regs xs 23 23%bv); [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia].
    + unfold MD_NEXT, MD_SIZE in *. lia.
  - rewrite R14. reflexivity.
  - rewrite R15. cbn [sv_denot]. rewrite tk_E_gnl. reflexivity.
  - rewrite R16. cbn [sv_denot]. rewrite tk_E_gnl, Z.add_0_r. reflexivity.
  - rewrite R17. reflexivity.
  - rewrite R6. reflexivity.
Qed.

Lemma tk_ov_at_ok : forall regs xs b a al, tk_rat regs b a al ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) tk_ov_at.
Proof.
  intros regs xs b a al (_ & _ & _ & R19 & R15 & R16 & R17).
  unfold tk_ov_at. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite R19. reflexivity.
  - rewrite R15. reflexivity.
  - rewrite R16. reflexivity.
  - rewrite R17. reflexivity.
Qed.

Lemma tk_ov_c1_ok : forall regs xs,
  getr regs 20 = w64 (tk_m c) -> getr regs 22 = w64 (tk_m c + MD_N_REQ) ->
  getr regs 24 = w64 (tk_shx (tk_m c + MD_N_REQ)) -> getr regs 23 = w64 SHADOW_OFF ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p))
    [(22%bv, SOff 20 0x2090); (24%bv, tk_shx_sv (SOff 20 0x2090))].
Proof.
  intros regs xs R20 R22 R24 R23.
  destruct tk_m_facts as (Hm0 & Hm1 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (U20 : U (tk_E c regs xs) (SOff 20 0x2090) = tk_m c + MD_N_REQ).
  { rewrite U_SOff, (tk_E_reg regs xs 20 20%bv) by (lia || reflexivity). rewrite R20. unfold w64.
    rewrite unsigned_lit_small by (unfold MD_SIZE in *; lia). unfold zcanon, M64, MD_N_REQ.
    apply Z.mod_small. unfold MD_SIZE in *. lia. }
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite R22. exact (tk_den_of_U _ _ _ U20).
  - rewrite R24. apply tk_den_shx; [exact U20 | | unfold MD_N_REQ, MD_SIZE in *; lia].
    apply (tk_U_reg regs xs 23 23%bv); [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia].
Qed.

(* ---- the frame regions ----------------------------------------------------------------------------------------- *)
Lemma tk_base_sp : forall regs mem md xs, tk_inv SK B c regs mem md ->
  base_val (tk_E c regs xs) (Some 2%nat) = tk_sp c - 144.
Proof.
  intros regs mem md xs (_ & _ & _ & Hsp & _).
  destruct tk_sp_rng as (S0 & S1 & _).
  cbn [base_val]. rewrite (tk_E_reg regs xs 2 2%bv ltac:(lia) eq_refl), Hsp. unfold w64.
  apply unsigned_lit_small. lia.
Qed.

Lemma tk_den_ext : forall regs xs j, (j < 17)%nat ->
  sv_denot (tk_E c regs xs) (SOff (32 + j) 0) = nth j (tk_ext c) (Z_to_bv 64 0).
Proof.
  intros regs xs j Hj. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply tk_E_ext. exact Hj.
Qed.

Ltac tk_wchunk HV :=
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?n 0))) =>
    let j := eval cbv in (n - 32)%nat in
    let w := eval cbn [nth tk_ext] in (nth j (tk_ext c) (Z_to_bv 64 0)) in
    apply (tk_chunk8 _ _ _ o n 0 w);
    [ apply (HV (o, w)); cbn [In tk_frame_vals tk_spill_vals];
      repeat (first [left; reflexivity | right])
    | change n with (32 + j)%nat; rewrite (tk_den_ext _ _ j) by (cbv; lia); reflexivity ]
  end.

(* the saved words, read only *)
Lemma tk_fr_ok : forall regs mem md xs, tk_inv SK B c regs mem md ->
  region_ok SEGS (tk_E c regs xs) (rdW W mem) tk_fr.
Proof.
  intros regs mem md xs HI. pose proof (tk_base_sp regs mem md xs HI) as Ub.
  pose proof HI as (_ & _ & _ & _ & _ & _ & HFV & _).
  destruct tk_sp_rng as (S0 & S1 & _).
  unfold tk_fr, tk_fr13, tk_ch, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  rewrite Forall_forall in HFV.
  repeat (apply Forall_cons; [tk_wchunk HFV|]). apply Forall_nil.
Qed.

(* the spill area, writable: the journal's window holds it *)
Lemma tk_frw_ok : forall regs mem md xs, tk_inv SK B c regs mem md ->
  region_ok SEGS (tk_E c regs xs) (rdW W mem) tk_frw.
Proof.
  intros regs mem md xs HI. pose proof (tk_base_sp regs mem md xs HI) as Ub.
  pose proof HI as (HJ & _).
  destruct tk_sp_bounds as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  destruct tk_sp_rng as (S0 & S1 & _).
  pose proof HJ as (_ & HXO2 & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  unfold tk_frw, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres.
  unfold TALK_AK, TALK_AFRAME, ESTACK in Hlo. lia.
Qed.

(* the spilled words, read only *)
Lemma tk_frs_ok : forall regs mem md xs b, tk_inv SK B c regs mem md -> tk_spilled c mem b ->
  getr regs 20 = w64 b -> 0 <= b -> b + 4 < 2 ^ 64 ->
  region_ok SEGS (tk_E c regs xs) (rdW W mem) tk_frs.
Proof.
  intros regs mem md xs b HI HSP R20 Hb0 Hb1. pose proof (tk_base_sp regs mem md xs HI) as Ub.
  destruct tk_sp_rng as (S0 & S1 & _).
  unfold tk_frs, tk_ch, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold tk_spilled in HSP. rewrite Forall_forall in HSP.
  apply Forall_cons; [tk_wchunk HSP|]. apply Forall_cons; [tk_wchunk HSP|].
  apply Forall_cons.
  { apply (tk_chunk8 _ _ _ 16 20 4 (w64 (b + 4))).
    - apply (HSP (16, w64 (b + 4))). unfold tk_spill_vals. cbn [In]. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite (tk_E_reg regs xs 20 20%bv) by (lia || reflexivity). rewrite R20. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity. }
  apply Forall_cons; [tk_wchunk HSP|]. apply Forall_cons; [tk_wchunk HSP|]. apply Forall_nil.
Qed.

(* ---- THE STATE BUILDER: a fresh symbolic state at a machine state that satisfies tk_inv ------------------------ *)
Lemma tk_st_ok : forall regs mem md xs pc ov rs ex,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) ov ->
  regions_wf rs = true -> Forall (region_ok SEGS (tk_E c regs xs) (rdW W mem)) rs ->
  pairwise_disjoint (tk_E c regs xs) rs -> atoms_ok (tk_E c regs xs) ex ->
  st_ok_pi SEGS VAL (tk_E c regs xs) (tk_ss pc ov rs ex)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros regs mem md xs pc ov rs ex HI H23 Hov Hwf Hrs Hd Hex.
  pose proof HI as (_ & _ & _ & Hsp & _).
  destruct tk_sp_rng as (S0 & S1 & S2 & _).
  rewrite restrict_mkst_fx. unfold tk_ss. apply pa_entry_st_ok_full.
  - apply tk_regs_ok_ovr; [apply regs_ok_Eimg_Ereg | exact Hov].
  - exact Hwf.
  - exact Hrs.
  - exact Hd.
  - split; [|split; exact I]. unfold tk_facts. cbn [f_atoms atoms_ok].
    refine (conj _ (conj _ (conj _ Hex))); unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite (tk_E_reg regs xs 2 2%bv ltac:(lia) eq_refl), Hsp. unfold w64.
      rewrite unsigned_lit_small by lia. change (2 ^ 4) with 16. lia.
    + rewrite (tk_E_reg regs xs 23 23%bv ltac:(lia) eq_refl), H23. unfold w64.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + rewrite tk_E_gnl. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* ---- the shadow transfers -------------------------------------------------------------------------------------- *)
(* a byte of the shadow band is a byte the call keeps *)
Lemma tk_shadow_kept : forall regs mem md, tk_inv SK B c regs mem md ->
  forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W) mem s = aview SEGS (w_H W) memc s.
Proof.
  intros regs mem md (_ & _ & _ & _ & _ & _ & _ & UN & _) s Hs.
  destruct tk_sp_rng as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  apply UN; [lia | unfold TALK_AK, TALK_AFRAME, ESTACK; lia |].
  intros He. destruct (tk_ewr_facts s He) as (_ & _ & [Hq|Hq]); lia.
Qed.

Lemma tk_ra_kept : forall regs mem md p n, tk_inv SK B c regs mem md ->
  0 <= p -> p + n <= kHighMemEnd ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n.
Proof.
  intros regs mem md p n HI Hp Hn H x Hx. destruct (H x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite (tk_shadow_kept regs mem md HI); [exact Hsv|].
  unfold shadow_of_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF, kHighMemEnd in *.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma tk_hull_kept : forall regs mem md p n, tk_inv SK B c regs mem md ->
  0 <= p -> p + n <= kHighMemEnd -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) memc) p n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
  intros regs mem md p n HI Hp Hn Hn0 H sx Hsx. rewrite (tk_shadow_kept regs mem md HI); [exact (H sx Hsx)|].
  unfold shadow_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF, kHighMemEnd in *.
  pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (p + n - 1) (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* g_nl keeps its bytes (talk writes none of them) *)
Lemma tk_gnl_kept : forall regs mem md a, tk_inv SK B c regs mem md ->
  LA_G_NL <= a < LA_G_NL + NK_SIZE -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) memc a.
Proof.
  intros regs mem md a (_ & _ & _ & _ & _ & _ & _ & UN & _) Ha.
  destruct tk_sp_rng as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  apply UN; [unfold LA_G_NL, NK_SIZE in *; lia | unfold TALK_AK, TALK_AFRAME, ESTACK, LA_G_NL, NK_SIZE in *; lia |].
  intros He. destruct (tk_ewr_facts a He) as (_ & Hg & _). exact (Hg Ha).
Qed.

Lemma tk_nlk_kept : forall regs mem md, tk_inv SK B c regs mem md -> anlk_at SEGS (rdW W mem) LA_G_NL kbs.
Proof.
  intros regs mem md HI. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & PR).
  tk_HC. destruct HNK as ((Hab & Hwr) & HL). split; [|exact HL]. split.
  - destruct Hab as (Ha0 & Ha1 & Hb). split; [exact Ha0|]. split; [exact Ha1|].
    intros i Hi. rewrite <- (Hb i Hi). apply (mbyte_of_aview SEGS (w_H W) (w_H W) memc mem).
    apply (tk_gnl_kept regs mem md); [exact HI|]. unfold LA_G_NL, NK_SIZE in *. lia.
  - intros i Hi. apply (writable_kept (w_H W) memc mem (LA_G_NL + i) (PR (LA_G_NL + i))). exact (Hwr i Hi).
Qed.

(* a field of g_nl at the current memory *)
Lemma tk_gnl_val : forall regs mem md off (n : nat), tk_inv SK B c regs mem md ->
  0 <= off -> (Z.to_nat off + n <= length kbs)%nat ->
  val_mem SEGS (rdW W mem) (LA_G_NL + off) n (rdn kbs off (Z.of_nat n)).
Proof.
  intros regs mem md off n HI Ho Hn. destruct (tk_nlk_kept regs mem md HI) as ((Hab & _) & _).
  exact (val_mem_of_abytes SEGS _ LA_G_NL kbs off n Hab Ho Hn).
Qed.

(* an SH entry on atom n from the range_addressable of the bytes it names *)
Lemma tk_shent_ok : forall E (m : word -> option byte) n lo hi x,
  U E tk_Bx = SHADOW_OFF -> U E (SOff n 0) = x -> lo <= hi ->
  (x + hi <= kLowMemEnd \/ kHighMemBeg <= x + lo) ->
  range_addressable (rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
  shent_ok SEGS tk_Bx E m (mkSHE n lo hi).
Proof.
  intros E m n lo hi x HB Hx Hlh Hz HR. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hx.
  split; [exact HR|]. intros a Ha.
  rewrite Z.min_l in Ha by exact Hlh. rewrite Z.max_r in Ha by exact Hlh.
  unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* ---- THE INVARIANT ACROSS A STEP that writes only below the saved words and bytes of the write set --------------- *)
Lemma tk_frame_offs : forall o w, In (o, w) (tk_frame_vals c) -> 0x28 <= o <= 0x88.
Proof.
  intros o w Hin. unfold tk_frame_vals in Hin.
  repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; lia|]). destruct Hin.
Qed.

Lemma tk_inv_step : forall regs mem md regs' mem' md' (Zs : Z -> Prop),
  tk_inv SK B c regs mem md ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem' md' (tc_k c) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, Zs a -> (tk_sp c - TALK_AK <= a < tk_sp c - 104) \/ tk_ewr c a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  tk_inv SK B c regs' mem' md'.
Proof.
  intros regs mem md regs' mem' md' Zs (HJ & Hfd & Hfs & Hsp & Hgp & Htp & HFV & UN & PR)
    HJ' Hfd' Hfs' UN' HZs PR' E2 E3 E4.
  destruct tk_sp_rng as (S0 & S1 & S2 & S3).
  assert (HnZ : forall a, tk_sp c - 104 <= a < tk_sp c -> ~ Zs a).
  { intros a Ha HZ. destruct (HZs a HZ) as [H|H]; [lia|].
    destruct (tk_ewr_facts a H) as (Hf & _). apply Hf. unfold TALK_AK, TALK_AFRAME, ESTACK. lia. }
  split; [exact HJ'|]. split; [congruence|]. split; [congruence|].
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  split.
  { rewrite Forall_forall in HFV |- *. intros [o w] Hin. cbn [fst snd].
    pose proof (tk_frame_offs o w Hin) as Ho. pose proof (HFV (o, w) Hin) as HV. cbn [fst snd] in HV.
    apply (val_mem_kept (w_H W) mem mem'); [|exact HV].
    intros k Hk. cbn in Hk. apply UN'; [lia|]. apply HnZ. lia. }
  split.
  { intros a Ha Hw He.
    assert (HZ : ~ Zs a) by (intros HZ; destruct (HZs a HZ) as [H|H]; [lia | exact (He H)]).
    rewrite (UN' a Ha HZ). exact (UN a Ha Hw He). }
  intros a Hp. exact (PR' a (PR a Hp)).
Qed.

(* ---- THE CALL OF checked_memcpy into the model block or a live buffer ------------------------------------------- *)
Lemma tk_preserved : forall regs regs2, aregs_preserved regs regs2 ->
  forall z, acallee_saved z -> getr regs2 (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z).
Proof. intros regs regs2 HP z Hz. exact (HP z Hz). Qed.

Lemma tk_intrin : forall op pc, aintrin_realizes SEGS B op pc ->
  forall regs mem md d x n raw,
  tk_inv SK B c regs mem md ->
  getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  tk_dst d n ->
  getr regs 1 = raw -> YK0s.ret_ok raw ->
  (match op with
   | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok SEGS W regs mem x n /\ (d + n <= x \/ x + n <= d) /\
             amem_range x n /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\
             (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n)
   | OSet => True end) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       tk_inv SK B c regs2 mem2 md2 /\ aregs_preserved regs regs2 /\
       (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (d + i) =
          match op with OCpy => aview SEGS (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (tk_sp c - 144 - ESTACK <= a < tk_sp c - 144) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)).
Proof.
  intros op pc AI regs mem md d x n raw HI Ha0 Ha1 Ha2 Hn Hdst Hra Hraw Hsrc.
  pose proof HI as (HJ & Hfd & Hfs & Hsp & H3 & H4 & HFV & UN & PR).
  pose proof HC as ((_ & HGX & _ & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hajw & _) & _).
  destruct tk_sp_bounds as (Hceil & Hlo & Hhi & H47 & Hsp16 & HXO).
  destruct tk_sp_rng as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (tk_dst_facts d n Hdst ltac:(lia)) as (Hd0 & Hdk & Hamd & Hdf & Hrad & Hhd & Hdw).
  (* the call's sp is the frame base tk_sp - 144 *)
  assert (Usp : spZ regs = tk_sp c - 144).
  { unfold spZ. rewrite Hsp. apply unsigned_lit_small. lia. }
  assert (H16' : spZ regs mod 16 = 0) by (rewrite Usp; exact S2).
  assert (Hlo' : tc_sp0 c - tc_STK c <= spZ regs - ESTACK)
    by (rewrite Usp; clear - Hlo; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia).
  assert (Hhi' : spZ regs <= tc_sp0 c) by (rewrite Usp; clear - Hhi; lia).
  assert (Hgp' : getr regs 3 = w64 (as_gp B)) by (rewrite H3; exact Hgp).
  assert (Htp' : getr regs 4 = w64 (as_tp B)) by (rewrite H4; exact Htp).
  assert (Hdn : d + n <= 2 ^ 63) by (clear - Hdk C4; lia).
  assert (Hra_d : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF d n)
    by (apply (tk_ra_kept regs mem md d n HI Hd0 ltac:(lia) Hrad)).
  assert (Hhull_d : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) d n)
    by (intros Hn0; apply (tk_hull_kept regs mem md d n HI Hd0 ltac:(lia) Hn0 (Hhd Hn0))).
  eapply SRr_mono.
  { refine (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low op pc AI (tc_G c) (tc_XO c) (tc_OUT c) W regs mem
      (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c) (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c)
      (tc_Sc c) md (tc_k c) d x n raw HGX HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn H16' Hlo' Hhi' Hgp' Htp' Hra Hraw _ Hamd Hra_d
      Hhull_d Hsrc).
    (* a destination byte is a byte of the write set talk_awr *)
    intros a Ha. destruct (Hdw a Ha) as [HW Hwr].
    destruct (Hajw a HW) as [[Haw Hxo] | [HG | HO]].
    - left. split; [exact Haw|]. split; [exact Hxo|]. rewrite Usp.
      clear - Hdf Ha. unfold apart_frame, tk_sp, TALK_AK, TALK_AFRAME, ESTACK in *. lia.
    - right; left. split; [exact HG|]. exact (writable_kept (w_H W) memc mem a (PR a) Hwr).
    - right; right. exact HO. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & H10 & Hres & Hfr & Hpres2 & Hsm).
  rewrite Usp in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
  assert (K : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs rr).
  { intros rr z -> Hz. exact (HP z Hz). }
  split.
  { apply (tk_inv_step regs mem md regs2 mem2 md2
      (fun a => (d <= a < d + n) \/ (tk_sp c - 144 - ESTACK <= a < tk_sp c - 144)) HI HJ2).
    - rewrite (same_but_materialized_wvb _ _ Hsm). exact (proj1 (wvb_fds_fs _ _ _)).
    - rewrite (same_but_materialized_wvb _ _ Hsm). exact (proj2 (wvb_fds_fs _ _ _)).
    - intros a Ha HZ. cbv beta in HZ.
      apply Hfr; [exact Ha | intros H; apply HZ; left; exact H | intros H; apply HZ; right; exact H].
    - intros a HZ. cbv beta in HZ. destruct HZ as [Ha | Ha].
      + right. exact (proj1 (Hdw a Ha)).
      + left. clear - Ha. unfold TALK_AK, TALK_AFRAME, ESTACK in *. lia.
    - exact Hpres2.
    - exact (K 2%bv 2 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
    - exact (K 3%bv 3 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
    - exact (K 4%bv 4 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)). }
  split; [exact HP|]. split; [exact Hres|].
  intros a Ha Hd Hw. exact (Hfr a Ha Hd Hw).
Qed.

(* the source premises of checked_memcpy for a source in g_nl's chunk queue (the payload of an attribute) *)
Lemma tk_src_gnl : forall regs mem md x n, tk_inv SK B c regs mem md ->
  getr regs 2 = w64 (tk_sp c - 144) -> LA_G_NL <= x -> x + n <= LA_G_NL + NK_CHUNK_LEN -> 0 <= n ->
  0 <= x /\ x + n <= 2 ^ 63 /\ src_ok SEGS W regs mem x n /\ amem_range x n /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n).
Proof.
  intros regs mem md x n HI Hsp Hx0 Hx1 Hn.
  destruct tk_sp_rng as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  tk_HC. destruct HNK as ((Hab & _) & HL).
  change (ard SEGS (rdW W memc)) with (aview SEGS (w_H W) memc) in HRAq, HHq.
  unfold LA_G_NL, NK_CHUNK, NK_CHUNK_LEN, NK_N_CHUNKS, NK_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - rewrite (tk_gnl_kept regs mem md a HI) by (unfold LA_G_NL, NK_SIZE; lia).
      destruct Hab as (_ & _ & Hb).
      rewrite <- (ard_aview SEGS W memc). unfold ard.
      replace a with (0x5dcac0 + Z.of_nat (Z.to_nat (a - 0x5dcac0))) by lia.
      rewrite Hb by lia.
      destruct (nth_error kbs (Z.to_nat (a - 0x5dcac0))) eqn:En; [discriminate|].
      apply nth_error_None in En. lia.
    - unfold spZ. rewrite Hsp. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia. }
  split; [unfold amem_range, kLowMemEnd; lia|].
  split.
  { apply (tk_ra_kept regs mem md x n HI ltac:(lia) ltac:(unfold kHighMemEnd; lia)).
    apply (range_addressable_sub _ _ (0x5dcac0 + 0) 262656); [exact HRAq | lia | lia]. }
  intros Hn0. apply (tk_hull_kept regs mem md x n HI ltac:(lia) ltac:(unfold kHighMemEnd; lia) Hn0).
  apply (rv_hull_sub _ (0x5dcac0 + 0) 262656); [exact HHq | lia | lia | exact Hn0].
Qed.

(* the source premises of checked_memcpy +0x12c for the request, whose bytes are as at the call *)
Lemma tk_src_req : forall regs mem md, tk_inv SK B c regs mem md ->
  getr regs 2 = w64 (tk_sp c - 144) ->
  (forall i, 0 <= i < tk_len c -> aview SEGS (w_H W) mem (tk_r c + i) = aview SEGS (w_H W) memc (tk_r c + i)) ->
  0 <= tk_r c /\ tk_r c + tk_len c <= 2 ^ 63 /\ src_ok SEGS W regs mem (tk_r c) (tk_len c) /\
  amem_range (tk_r c) (tk_len c) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (tk_r c) (tk_len c) /\
  (0 < tk_len c -> shadow_hull_vis (aview SEGS (w_H W) mem) (tk_r c) (tk_len c)).
Proof.
  intros regs mem md HI Hsp HK.
  destruct tk_sp_rng as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct tk_r_facts as (R0 & RL & RA & RH & RF & RP & RR & RV & (Hb0 & Hb1 & Hb) & HL).
  split; [lia|]. split; [unfold kHighMemEnd in *; lia|]. split.
  { intros a Ha. split.
    - replace a with (tk_r c + (a - tk_r c)) by lia. rewrite (HK (a - tk_r c)) by lia.
      rewrite <- (ard_aview SEGS W memc). unfold ard.
      replace (tk_r c + (a - tk_r c)) with (tk_r c + Z.of_nat (Z.to_nat (a - tk_r c))) by lia.
      rewrite Hb by lia.
      destruct (nth_error (tc_req c) (Z.to_nat (a - tk_r c))) eqn:En; [discriminate|].
      apply nth_error_None in En. lia.
    - unfold spZ. rewrite Hsp. unfold w64. rewrite unsigned_lit_small by lia.
      unfold apart_frame, tk_sp, TALK_AK, TALK_AFRAME, ESTACK in *. lia. }
  split; [exact RA|]. split.
  { apply (tk_ra_kept regs mem md (tk_r c) (tk_len c) HI R0 ltac:(lia) RR). }
  intros Hn0. apply (tk_hull_kept regs mem md (tk_r c) (tk_len c) HI R0 ltac:(lia) Hn0 (RV Hn0)).
Qed.
End w.
