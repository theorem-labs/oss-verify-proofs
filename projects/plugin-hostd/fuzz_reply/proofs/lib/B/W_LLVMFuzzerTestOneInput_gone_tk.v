(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   its transport kit (the image-B twin of lib/A/W_LLVMFuzzerTestOneInput_gone_tk.v on a working branch
   32b23a20c3e): the frame / model / input / rom / jump-table facts kept across a step that keeps every byte below
   alloc_ceiling + 8.  COPIED from image B's latch walk, lib/B/W_LLVMFuzzerTestOneInput_latch.v on
   a working branch ee519e5e2f5 (Section kit :75-268 and the kit lemmas of Section w :299-465;
   lt_ -> gk_, CEIL8 -> GK_CEIL8), exactly as A's arm copied A's latch, so this piece does not import another piece's
   file; plus gk_keep_lo_w / gk_keep_hi_w / gk_gframe_kept, the same three facts for a callee window of any size and for
   the base's gframe (the frame with the fake frame's shadow as a parameter). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
(* RelocB's sink-instance guard (after the Import of YE2k): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's stack budget, from the generated lib/B/YCfn.v (LLVMF_STK 32768), as the cut names it *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Definition GK_CEIL8 : Z := alloc_ceiling + 8.
Definition gk_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= GK_CEIL8) fp.
Lemma gk_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* a bound on a range of fuzz_reply.asan-ubsan's globals, or on errno from the premises *)
Ltac gk_low :=
  cbn [fst snd gfp]; unfold GK_CEIL8 in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof gk_ceil_lo; lia.

Lemma gk_fp_low_nil : gk_fp_low []. Proof. constructor. Qed.
Lemma gk_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= GK_CEIL8 -> gk_fp_low fp -> gk_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
Lemma gk_fp_low_app : forall f1 f2, gk_fp_low f1 -> gk_fp_low f2 -> gk_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma gk_fp_low_forall : forall fp, gk_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= GK_CEIL8).
Proof. intros fp. unfold gk_fp_low. apply Forall_forall. Qed.
Lemma gk_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) -> gk_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite gk_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.

(* a live block: its bytes, and the 7 bytes of alignment slack a key's text may carry past them *)
Lemma gk_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma gk_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma gk_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma gk_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, gk_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma gk_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
Lemma gk_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= GK_CEIL8 ->
  gk_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : gk_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite gk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (gk_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold GK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply gk_fp_low_cons; [cbn; lia | cbn; lia|]. apply gk_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply gk_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (gk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply gk_fp_low_cons; [cbn; lia | | apply gk_fp_low_nil].
    cbn [gfp fst snd]. rewrite gk_bzs_len, length_app, gk_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold GK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma gk_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= GK_CEIL8 ->
  gk_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (gk_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (gk_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (gk_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (gk_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply gk_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply gk_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite gk_bzs_len, Hpj. unfold APARTIAL, GK_CEIL8 in *. lia.
    + apply gk_fp_low_app; [exact A1|]. apply gk_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
Lemma gk_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  gk_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : gk_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite gk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (gk_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold GK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply gk_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply gk_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (gk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply gk_fp_low_cons; [cbn; lia | | apply gk_fp_low_nil].
      cbn [gfp snd]. rewrite gk_bzs_len, length_app. unfold GK_CEIL8 in *. lia.
    + apply gk_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (gk_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite gk_bzs_len, gk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold GK_CEIL8. pose proof gk_ceil_lo. lia. }
        destruct (gk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold GK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan-ubsan's globals (fr_globals_b, the cut's fr_RG) ---- *)
Lemma gk_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_globals_b ly S W mem G es ->
  gk_fp_low (arelay_fp fr_globals_b G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (gk_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : gk_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite gk_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (gk_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite gk_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (gk_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply gk_fp_low_cons; [gk_low | gk_low|].
    apply gk_fp_low_cons; [gk_low | gk_low|].
    apply gk_fp_low_cons; [gk_low | gk_low|].
    apply gk_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, GK_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma gk_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_globals_b ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= GK_CEIL8 ->
  gk_fp_low (aout_fp B fr_globals_b cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply gk_fp_low_cons; [gk_low | gk_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply gk_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (gk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply gk_fp_low_cons; [cbn; lia | cbn; unfold GK_CEIL8 in *; lia | apply gk_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
End kit.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_base.

Section gk_w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Lemma gk_ceil_hi : GK_CEIL8 < 2 ^ 64.
Proof. unfold GK_CEIL8. pose proof asan_consts as (C1 & _). lia. Qed.
Lemma gk_keep_lo : forall (W W' : world segs) mem mem' F,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F - 16 <= a < F) -> abyte_kept W mem W' mem' a) ->
  GK_CEIL8 <= F - 16 -> forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' F HK HF a Ha. pose proof gk_ceil_hi. apply HK; lia. Qed.
Lemma gk_keep_hi : forall (W W' : world segs) mem mem' F,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F - 16 <= a < F) -> abyte_kept W mem W' mem' a) ->
  0 <= F -> forall a, F <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' F HK HF a Ha. apply HK; lia. Qed.
Lemma gk_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= GK_CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply gk_akept_of_low; [exact HK|].
  apply gk_fp_low_cons; [cbn; lia | cbn; lia | apply gk_fp_low_nil].
Qed.
Lemma gk_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= GK_CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.

(* ---- the model ---- *)
Lemma gk_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= GK_CEIL8 ->
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= GK_CEIL8)
      by (unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (gk_asrc B LAWS ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (gk_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (gk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (gk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (gk_arelay B LAWS ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (gk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (gk_aout B LAWS ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (gk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply gk_akept_rng; [exact KEEP | cbn; lia | unfold GK_CEIL8; cbn; pose proof gk_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply gk_akept_rng; [exact KEEP | cbn; lia | unfold GK_CEIL8; cbn; pose proof gk_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply gk_akept_rng; [exact KEEP | cbn; lia | unfold GK_CEIL8; cbn; pose proof gk_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, GK_CEIL8 in *. pose proof gk_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, GK_CEIL8 in *. pose proof gk_ceil_lo. lia.
Qed.

(* ---- the frame, the fake frame and its shadow ---- *)
Lemma gk_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* B's frame (no `full` flag): the saved registers above F, the fourteen slots F+32 .. F+184 the prologue stores
   (0x844ac-0x845d8), all at or above F; the fake frame's header and its shadow, below alloc_ceiling *)
Lemma gk_aframe_kept : forall cx FF (W W' : world segs) mem mem',
  aframe_at cx FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - 16 <= a < lf_F cx) -> abyte_kept W mem W' mem' a) ->
  GK_CEIL8 <= lf_F cx - 16 -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= GK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= GK_CEIL8 ->
  aframe_at cx FF W' mem'.
Proof.
  intros cx FF W W' mem mem'
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20
     & A21)
    HK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof gk_ceil_hi as HC64. pose proof gk_ceil_lo as HCL.
  assert (HFpos : 0 <= lf_F cx) by lia.
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a)
    by (apply (gk_keep_lo W W' mem mem' (lf_F cx) HK HLO)).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (apply (gk_keep_hi W W' mem mem' (lf_F cx) HK HFpos)).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W mem); [|exact A2]. intros x Hx. apply KH. lia. }
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A3]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A4]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A5]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A6]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A7]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A8]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A9]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A10]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A11]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A12]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A13]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A14]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A15]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A16]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A17]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A18]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A19]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A20]|].
  split.
  { apply (akept_garr8 W mem); [|exact (proj1 A21)]. intros x Hx.
    unfold fake_shadow in Hx. cbn [length] in Hx. apply KL. lia. }
  apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact (proj2 A21)].
Qed.

(* ---- the input block, the read-only image, the jump table ---- *)
Lemma gk_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (gk_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold GK_CEIL8. lia.
Qed.
Lemma gk_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof gk_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold GK_CEIL8, kLowMemEnd in *; lia))).
Qed.
Lemma gk_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia.
Qed.

(* ---- the same for a callee window [F - w, F) of any size (B's latch has w = 16, check_bounded's frame) ---- *)
Lemma gk_keep_lo_w : forall (W W' : world segs) mem mem' F w,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F - w <= a < F) -> abyte_kept W mem W' mem' a) ->
  GK_CEIL8 <= F - w -> forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' F w HK HF a Ha. pose proof gk_ceil_hi. apply HK; lia. Qed.
Lemma gk_keep_hi_w : forall (W W' : world segs) mem mem' F w,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F - w <= a < F) -> abyte_kept W mem W' mem' a) ->
  0 <= F -> forall a, F <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' F w HK HF a Ha. apply HK; lia. Qed.
(* the base's gframe (any fake shadow sh of 16 bytes) across such a step: gk_aframe_kept's proof *)
Lemma gk_gframe_kept : forall cx sh FF (W W' : world segs) mem mem' w,
  gframe cx sh FF W mem -> length sh = 16%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - w <= a < lf_F cx) -> abyte_kept W mem W' mem' a) ->
  0 <= w -> GK_CEIL8 <= lf_F cx - w -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= GK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= GK_CEIL8 ->
  gframe cx sh FF W' mem'.
Proof.
  intros cx sh FF W W' mem mem' w
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20
     & A21 & A22) Hsh HK Hw0 HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof gk_ceil_hi as HC64. pose proof gk_ceil_lo as HCL.
  assert (HFpos : 0 <= lf_F cx) by (unfold GK_CEIL8 in *; lia).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a)
    by (apply (gk_keep_lo_w W W' mem mem' (lf_F cx) w HK HLO)).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (apply (gk_keep_hi_w W W' mem mem' (lf_F cx) w HK HFpos)).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W mem); [|exact A2]. intros x Hx. apply KH. lia. }
  do 14 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | assumption]|]).
  do 3 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A20]|].
  split.
  { apply (akept_garr8 W mem); [|exact A21]. intros x Hx.
    rewrite Hsh in Hx. apply KL. lia. }
  apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A22].
Qed.
End gk_w.
